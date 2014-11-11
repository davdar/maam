{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Process where

import Data.Maybe
import System.IO.Unsafe
import Text.Pandoc
import Text.Pandoc.Walk
import Data.Monoid
import Control.Monad
import System.Process
import Text.Regex
import Text.Regex.TDFA
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Text.IO as T
import Data.List
import Tables
import Control.Monad.Writer
import Debug.Trace
import Data.List.Split

data MatchMode = 
    Word      -- "an" will not match in "Dan"
  | Anywhere  -- "+" will match in "a+b"
  deriving (Read, Show)

mathttNames :: [Text]
mathttNames =
    map (snd . head)
  $ tableRows 
  $ unsafePerformIO 
  $ parseTableIO "Process_mathttNames.tbl"

mathTTMacros :: [(Text,Text,MatchMode)]
mathTTMacros = flip map mathttNames $ \ n ->
  (n, T.concat ["\\operatorname{\\mathtt{", n, "}}" ], Word)

macros :: [(Text,Text,MatchMode)]
macros = 
    map extractMacro
  $ tableRows
  $ unsafePerformIO 
  $ parseTableIO "Process_macros.tbl"
  where
    extractMacro :: [(Text, Text)] -> (Text, Text, MatchMode)
    extractMacro row = fromJust $ do
      s <- lookup "Search For" row
      r <- lookup "Replace With" row
      m <- liftM (read . T.unpack) $ lookup "Match Mode" row
      return (s, r, m)

allMacros :: [(Text,Text,MatchMode)]
allMacros = macros ++ mathTTMacros

regexmeta :: [Text]
regexmeta = [ "\\" , "|" , "(" , ")" , "[" , "]" , "{" , "}" , "^" , "$" , "*" , "+" , "?" , "." ]

escapeRegex :: Text -> Text
escapeRegex = appEndo $ execWriter $ forM_ (reverse regexmeta) $ \ c -> do
  tell $ Endo $ T.replace c $ T.concat ["\\", c]

macroText :: Text -> Text
macroText = appEndo $ execWriter $ forM_ (reverse allMacros) $ \ (s,r,m) -> do
  let escaped = escapeRegex s
      withMode = case m of
        Word -> T.concat ["\\<",escaped,"\\>"]
        Anywhere -> escaped
      regex = mkRegex $ T.unpack withMode
      replace = T.unpack $ T.concat [" ", r, " "]
  tell $ Endo $ \ t -> T.pack $ subRegex regex (T.unpack t) replace

main :: IO ()
main = do
  s <- T.readFile "pldi15.markdown"
  let pre = preProcess s
      md = readMarkdown def $ T.unpack pre
      post = postProcess md
  system "mkdir -p tmp/autogen"
  T.writeFile "tmp/autogen/pldi15.markdown.pre" pre
  T.writeFile "tmp/autogen/pldi15.markdown.tex" $ T.pack $ writeLaTeX def post

-- Pre Processing {{{

preProcess :: Text -> Text
preProcess = addPars . stripComments

stripComments :: Text -> Text
stripComments = newlines . map fixEmpties . filter (not . isComment) . T.lines
  where
    isComment :: Text -> Bool
    isComment s = T.unpack s =~ ("^\\s*--" :: String)
    fixEmpties :: Text -> Text
    fixEmpties s = if T.unpack s =~ ("^\\s*$" :: String) then "" else s

addPars :: Text -> Text
addPars = newlines . {- addPar . -} T.lines
  where
    addPar :: [Text] -> [Text]
    addPar = intercalate ["\n<!-- -->","\\par","<!-- -->\n"] . splitOn [""]

-- }}}

-- Post Processing {{{

postProcess :: Pandoc -> Pandoc
postProcess = walkInline . walkBlocks
  where
    walkBlocks :: Pandoc -> Pandoc
    walkBlocks = walk $ \ (b :: Block) -> case b of
      CodeBlock (_,[c],_) s 
        | "align" `isPrefixOf` c -> alignBlock $ T.pack s
        | "indent" `isPrefixOf` c -> indentBlock $ T.pack s
      CodeBlock a s -> b
      _ -> b
    walkInline :: Pandoc -> Pandoc
    walkInline = walk $ \ (i :: Inline) -> case i of
      Code _ s -> RawInline (Format "latex") $ T.unpack $ T.concat
        [ "$"
        , macroText $ T.pack s
        , "$"
        ]
      _ -> i

-- Align {{{

alignBlock :: Text -> Block
alignBlock s = 
  let (cols,lines) = alignLines $ T.lines s
  in RawBlock (Format "latex") $ T.unpack $ newlines
    [ T.concat [ "\\small\\begin{alignat*}{" , T.pack (show cols) , "}" ]
    , newlines lines
    , "\\end{alignat*}\\normalsize"
    ] 
alignLines :: [Text] -> (Int,[Text])
alignLines s = 
  let (ns,lines) = unzip $ map alignLine s
  in (maximum ns, addAlignEndings lines)
alignLine :: Text -> (Int,Text)
alignLine s = 
  let stripped = T.strip s
      cols = filter ((/=) "") . map T.strip $ T.splitOn "  " stripped
      len = length cols
  in (len, format True cols)
  where
    format :: Bool -> [Text] -> Text
    format _ [] = ""
    format _ [t] = macroText t
    format i (t:ts) = T.unwords
      [ macroText t
      , if i then "&" else "&&"
      , format False ts
      ]

-- }}}

-- Indent {{{

indentBlock :: Text -> Block
indentBlock s =
  let lines = map indentLine $ T.lines s
  in RawBlock (Format "latex") $ T.unpack $ newlines
    [ "\\small\\begin{align*}"
    , newlines $ addAlignEndings lines
    , "\\end{align*}\\normalsize"
    ]

indentLine :: Text -> Text
indentLine t =
  let (whites, text) = T.span ((==) ' ') t
  in T.unwords
    [ T.concat [ "&\\hspace{", T.pack $ show $ T.length whites, "em}" ]
    , macroText text
    ]

-- }}}

-- }}}

-- Helpers {{{

newlines :: [Text] -> Text
newlines = T.intercalate "\n"

mapAllButLast :: (a -> a) -> [a] -> [a]
mapAllButLast _ [] = []
mapAllButLast _ [a] = [a]
mapAllButLast f (x:xs) = f x:mapAllButLast f xs

addAlignEndings :: [Text] -> [Text]
addAlignEndings = {- mapAllButLast -} map $ \ t -> T.unwords [t, "\\\\"]

-- }}}
