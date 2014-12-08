module Lang.Lam.Parser where

import FP
import FP.Parser
import qualified FP.Pretty as P
import Lang.Lam.Syntax
import Lang.Common
import qualified Prelude as Prelude

data TokenType =
    White
  | Num
  | Key
  | Id
  deriving (Eq, Ord)
instance Pretty TokenType where
  pretty White = P.con "W"
  pretty Num = P.con "N"
  pretty Key = P.con "K"
  pretty Id = P.con "I"
data Token = Token
  { tokenType :: TokenType
  , tokenVal :: String
  }
  deriving (Eq, Ord)
instance Pretty Token where
  pretty (Token t s) = P.app [pretty t, pretty s]

-- Lexing {{{

white :: Parser Char String
white = fromChars ^$ oneOrMoreList $ satisfies isSpace

litTok :: String -> Parser Char String
litTok = fromChars ^. word . toChars

numLit :: Parser Char String
numLit = fromChars ^$ oneOrMoreList $ satisfies isDigit

ident :: Parser Char String
ident = fromChars ^$ oneOrMoreList $ satisfies (isLetter \/ isDigit \/ (==) '-' \/ (==) '_')

token :: Parser Char Token
token = mconcat
  [ Token White ^$ white
  , Token Key ^$ mconcat $ map litTok
      [ "("
      , ")"
      , "let"
      , ":="
      , "in"
      , "lam"
      , "."
      , "begin"
      , "end"
      , "if"
      , "then"
      , "else"
      , "T"
      , "F"
      , "+"
      , "*"
      , "-"
      ]
  , Token Num ^$ numLit
  , Token Id ^$ ident
  ] 

-- }}}

-- Parsing {{{

key :: String -> Parser Token ()
key = void . lit . Token Key

litExp :: Parser Token Lit
litExp = mconcat
  [ I . Prelude.read . toChars . tokenVal ^$ satisfies ((==) Num . tokenType)
  , const (B True) ^$ lit $ Token Key "T"
  , const (B False) ^$ lit $ Token Key "T"
  ]

nameExp :: Parser Token Name
nameExp = Name . tokenVal ^$ satisfies ((==) Id . tokenType)

letExp :: Parser Token Exp
letExp = ff ^$ pre 0 "let" letin exp
  where
    ff (xe1s, e2) = foldrOn xe1s e2 $ \ (x, e1) e -> Fix $ Let x e1 e

letin :: Parser Token (Name, Exp)
letin = closed (key "let") (key "in") $ do
  x <- nameExp
  key ":="
  e1 <- exp
  return (x, e1)

lamExp :: Parser Token Exp
lamExp = ff ^$ pre 0 "lam" lamdot exp
  where
    ff (bs, e) = foldrOn bs e $ Fix .: Lam

lamdot :: Parser Token Name
lamdot = closed (key "lam") (key ".") nameExp

appExp :: Parser Token Exp
appExp = juxtL 100 "app" exp $ Fix .: App

exp :: Parser Token Exp
exp = mconcat
  [ Fix . Lit ^$ litExp
  , Fix . Var ^$ nameExp
  , closed (key "(") (key ")") exp
  , letExp
  , lamExp
  , appExp
  ]

-- }}}

whitespaceFilter :: Token -> Bool
whitespaceFilter = (==) White . tokenType

parseE :: (Pretty a) => Parser Token a -> String -> ParseError Char Token a :+: a
parseE p input = parse token whitespaceFilter (final p) $ toChars input

parseExp :: String -> ParseError Char Token Exp :+: Exp
parseExp = parseE exp
