{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

module Process where

import Text.Pandoc
import Text.Pandoc.Walk
import Data.Monoid
import Control.Monad
import System.Process
import Text.Regex.TDFA
import Text.Regex.TDFA.Text
import qualified Data.Text as T
import Data.Text (Text)
import qualified Data.Text.IO as T
import Data.List

varNames :: [Text]
varNames =
  [ "Var"
  , "Atom"
  , "IOp"
  , "EOp"
  , "Exp"
  , "Env"
  , "Store"
  , "Time"
  , "KAddr"
  , "OAddr"
  , "KStore"
  , "M"
  , "bind"
  , "return"
  , "bind-unit"
  , "bind-associativity"
  ]

varNameMacros :: [(Text,Text)]
varNameMacros = flip map varNames $ \ n ->
  (n, T.concat ["\\mathtt{", n, "}" ])

-- These get applied in reverse order!
macroTable :: [(Text, Text)]
macroTable =
  varNameMacros
  ++
  -- math
  [ ( "ρ"      , " \\rho "             )
  , ( "α"      , " \\alpha "           )
  , ( "β"      , " \\beta "            )
  , ( "τ"      , " \\tau "             )
  , ( "σ"      , " \\sigma "           )
  , ( "ς"      , " \\varsigma "        )
  , ( "Σ"      , " \\Sigma "           )
  , ( "θ"      , " \\theta "           )
  , ( "κ"      , " \\kappa "           )
  , ( "μ"      , " \\mu "              )
  , ( "π"      , " \\pi "              )
  , ( "ℤ"      , " \\Int "             )
  , ( "×"      , " \\times "           )
  , ( "⇀"      , " \\rightharpoonup "  ) 
  , ( "→"      , " \\rightarrow "      ) 
  , ( "□"      , " \\square "          ) 
  , ( "~~>"    , " \\rightsquigarrow " )
  , ( "↦"      , " \\mapsto "          )
  , ( "∷"      , " \\cons "            )
  , ( "≠"      , " \\neq "             )
  , ( "≟"      , " \\stackrel{?}{=}"   )
  , ( "𝒫"      , " \\mathcal{P}"       )
  , ( "∪"      , " \\cup "             )
  , ( "∀"      , " \\forall "          )
  , ( "where"  , " \\where "           )
  , ( "when"   , " \\when "            )
  -- other
  , ( "λIF"    , " \\lamif "           )
  , ( "PVal"   , " \\PVal "            )
  , ( "AVal"   , " \\AVal "            )
  , ( "CVal"   , " \\CVal "            )
  , ( "OStore" , " \\OStore "          )
  , ( "OAddr"  , " \\OAddr "           )
  , ( "KStore" , " \\KStore "          )
  , ( "KAddr"  , " \\KAddr "           )
  -- superscription
  , ( "ᵍᶜ"     , "^{gc}"               ) 
  , ( "ᵗ"      , "^t "                 )
  , ( "ᵐ"      , "^m "                 )
  , ( "ᶠⁱ"     , "^{fi}"               )
  , ( "ᵖˢ"     , "^{ps}"               )
  , ( "ᶠˢ"     , "^{fs}"               )
  -- subscript ion
  , ( "₀"      , "_0 "                 )
  , ( "₁"      , "_1 "                 )
  , ( "₂"      , "_2 "                 )
  , ( "₃"      , "_3 "                 )
  , ( "ₙ"      , "_n "                 )
  , ( "ₘ"      , "_m "                 )
  , ( "ᵢ"      , "_i "                 )
  , ( "ⱼ"      , "_j "                 )
  -- punctuati on (do these before subscription)
  , ( "⟨"      , " \\langle "          )
  , ( "⟩"      , " \\rangle "          )
  , ( "["      , " \\lbrack "          )
  , ( "]"      , " \\rbrack "          )
  , ( "⟦"      , " \\llbracket "       ) 
  , ( "⟧"      , " \\rrbracket "       ) 
  , ( "∈"      , " \\In "              )
  , ( "|"      , " \\alt "             )
  , ( ";"      , " \\semicolon "       )
  , ( "_"      , " \\_ "               )
  -- object la nguage (must come before punctuation)
  , ( "if0"    , " \\objifz "          )
  , ( "[λ]"    , " \\objlambda "       )
  , ( "[+]"    , " \\objplus "         )
  , ( "[-]"    , " \\objminus "        )
  , ( "⊕"      , " \\oplus "           )
  , ( "⊙"      , " \\odot "            )
  , ( "@"      , " \\objapply "        )
  -- first cur ly brackets (must come before object language)
  , ( "{"      , " \\{ "               )
  , ( "}"      , " \\} "               )
  ]

macroText :: Text -> Text
macroText =  appEndo $ mconcat $ map (Endo . uncurry T.replace) macroTable

main :: IO ()
main = do
  s <- T.readFile "pldi15.markdown"
  let pre = preProcess s
      md = readMarkdown def $ T.unpack pre
      post = postProcess md
  system "mkdir -p tmp/autogen"
  T.writeFile "tmp/autogen/pldi15.markdown.tex" $ T.pack $ writeLaTeX def post

-- Pre Processing {{{

preProcess :: Text -> Text
preProcess = stripComments

stripComments :: Text -> Text
stripComments = newlines . filter (not . isComment) . T.lines
  where
    isComment :: Text -> Bool
    isComment s = T.unpack s =~ ("^\\s*--" :: String)

-- }}}

-- Post Processing {{{

postProcess :: Pandoc -> Pandoc
postProcess = walkInline . walkBlocks
  where
    walkBlocks = walk $ \ (b :: Block) -> case b of
      CodeBlock (_,[c],_) s 
        | "align" `isPrefixOf` c -> alignBlock $ T.pack s
        | "indent" `isPrefixOf` c -> indentBlock $ T.pack s
      CodeBlock a s -> b
      _ -> b
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
    [ T.concat [ "\\begin{alignat*}{" , T.pack (show cols) , "}" ]
    , newlines lines
    , "\\end{alignat*}"
    ] 
alignLines :: [Text] -> (Int,[Text])
alignLines s = 
  let (ns,lines) = unzip $ map alignLine s
  in (maximum ns, lines)
alignLine :: Text -> (Int,Text)
alignLine s = 
  let stripped = T.strip s
      cols = filter ((/=) "") . map T.strip $ T.splitOn "  " stripped
      len = length cols
  in (len, format True cols)
  where
    format :: Bool -> [Text] -> Text
    format _ [] = "\\\\"
    format _ [t] = T.unwords
      [ macroText t
      , "\\\\"
      ]
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
    [ "\\begin{align*}"
    , newlines lines
    , "\\end{align*}"
    ]

indentLine :: Text -> Text
indentLine t =
  let (whites, text) = T.span ((==) ' ') t
  in T.unwords
    [ T.concat [ "&\\hspace{", T.pack $ show $ T.length whites, "em}" ]
    , macroText text
    , "\\\\"
    ]

-- }}}

-- }}}

-- Helpers {{{

newlines :: [Text] -> Text
newlines = T.intercalate "\n"

-- }}}
