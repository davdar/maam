module Darkdown.Parser where

import FP hiding (pluck)
import FP.Parser
import FP.DerivingPretty ()

data Header = Header
  { headerLevel :: Integer
  , headerText :: String
  }
makePrettySum ''Header

data Inline =
    RawInline String
  | EmphInline Inline
  | BoldInline Inline
  | EmphBoldInline Inline
  | LinkInline Inline
  | FootnoteInline Inline
  | CitationInline Inline
  | ReferenceInline Inline
  | VerbatimInline String
makePrettySum ''Inline

data ListType =
    Itemize String
  | Enum
makePrettySum ''ListType

data ListEntry = ListEntry
  { listEntryContents :: [Inline]
  , listEntryChildren :: [ListEntry]
  }
makePrettySum ''ListEntry

data List = List
  { listType :: ListType
  , listItems :: [ListEntry]
  }
makePrettySum ''List

data Block =
    HeaderBlock Header
  | TextBlock [Inline]
  | ListBlock List
  | VerbatimBlock String
makePrettySum ''Block

data Dark = Dark
  { darkBlocks :: [Block]
  }

data Chunk = Chunk
  { chunkIndent :: Integer
  , chunkContents :: String
  }
makePrettySum ''Chunk

data Section = Section
  { sectionChunks :: [Chunk]
  }
makePrettySum ''Section

chunkBlock :: Parser Char [Section]
chunkBlock = do
  s <- many $ lit ' '
  mconcat
    [ do
        void $ lit '\n'
        chunkBlock
    , do
        t0 <- satisfies $ not . (?) "\n-"
        t <- undefined -- fromChars ^$ many $ satisfies $ (/=) '\n'
        void $ lit '\n'
        (cs, ss) <- chunkEndline
        undefined -- return $ Section (Chunk (length s) (cons t0 t) : cs) : ss
    , end >> return []
    ]

chunkEndline :: Parser Char ([Chunk], [Section])
chunkEndline = do
  s <- many $ lit ' '
  mconcat
    [ do
        void $ lit '\n'
        ss <- chunkBlock
        return ([], ss)
    , do 
        t <- fromChars ^$ oneOrMoreList $ satisfies $ (/=) '\n'
        void $ lit '\n'
        (cs, ss) <- chunkEndline
        return (Chunk (length s) t : cs,  ss)
    , end >> return ([], [])
    ]

parseHeaderBlock :: Parser Chunk Header
parseHeaderBlock = do
  Chunk i s <- pluck
  guard $ i == 0
  sumElim (const mbot) return $ parseFinalOn (toChars s) $ do
    void $ lit '#'
    subs <- many $ string "-|" 
    rest <- many pluck
    return $ Header (length subs) $ fromChars rest

parseTextBlockAccum :: Parser Chunk String
parseTextBlockAccum = concat . intersperse " " ^$ many $ do
  Chunk i s <- pluck
  guard $ i == 0
  return s

data InlineToken =
    TextInlineToken String
  | EscapedInlineToken Char
  | EmphasisInlineToken
  | BoldInlineToken
  | BoldEmphInlineToken
  | LinkInlineToken
  | FootnoteInlineToken Int
  | CitationInlineToken
  | DirectReferenceInlineTokenL
  | DirectReferenceInlineTokenR
  | IndirectReferenceInlineTokenL
  | IndirectReferenceInlineTokenR
  | VerbatimInlineToken

inlineToken :: Parser Char InlineToken
inlineToken = mconcat
  [ TextInlineToken . fromChars ^$ oneOrMoreList $ satisfies $ not . (?) "+|[]()" ]

parseInline :: Parser Char Inline
parseInline = undefined

parseTextBlock :: Parser Chunk [Inline]
parseTextBlock = do
  s <- parseTextBlockAccum
  sumElim (const mbot) return $ parseFinal (many parseInline) $ toChars s

parseListBlock :: Parser Chunk List
parseListBlock = undefined

parseVerbatimBlock :: Parser Chunk String
parseVerbatimBlock = undefined

parseChunks :: Parser Chunk Block
parseChunks = mconcat
  [ HeaderBlock ^$ parseHeaderBlock
  , TextBlock ^$ parseTextBlock
  , ListBlock ^$ parseListBlock
  , VerbatimBlock ^$ parseVerbatimBlock
  ]

parse :: String -> Doc :+: Dark
parse s = do
  ss <- mapInl pretty $ parseFinal chunkBlock $ toChars s
  Dark ^$ mapOnM ss $ \ (Section cs) ->
    mapInl pretty $ parseFinal parseChunks cs
