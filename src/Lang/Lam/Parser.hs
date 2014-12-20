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
makePrettyUnion ''Token

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
  , const (B False) ^$ lit $ Token Key "F"
  ]

nameExp :: Parser Token Name
nameExp = Name . tokenVal ^$ satisfies ((==) Id . tokenType)

letExp :: Mix (Parser Token) Exp
letExp = pre (\ (x, e1) e2 -> Fix $ Let x e1 e2) $ do
  key "let"
  x <- nameExp
  key ":="
  e1 <- exp
  key "in"
  return (x, e1)

lamExp :: Mix (Parser Token) Exp
lamExp = pre (Fix .: Lam) $ do
  key "lam"
  x <- nameExp
  key "."
  return x

ifExp :: Mix (Parser Token) Exp
ifExp = pre (\ (e1, e2) e3 -> Fix $ If e1 e2 e3) $ do
  key "if"
  e1 <- exp
  key "then"
  e2 <- exp
  key "else"
  return (e1, e2)

appExp :: Mix (Parser Token) Exp
appExp = infl (\ e1 () e2 -> Fix $ App e1 e2) (return ())

exp :: Parser Token Exp
exp = build lits (fromList mixes)
  where
    lits = 
      [ Fix . Lit ^$ litExp
      , Fix . Var ^$ nameExp
      , between (key "(") (key ")") exp
      ]
    mixes =
      [ ( 0   , [ letExp 
                , lamExp 
                , ifExp 
                ] )
      , ( 100 , [ appExp ] )
      ]

testp0 :: String
testp0 = "lam x . if x then let x := 4 in x y z else w (x y) z"

testp1 :: String
testp1 = "(lam x . x) ((lam x . x) (lam x . x))"

-- }}}

whitespaceFilter :: Token -> Bool
whitespaceFilter = (==) White . tokenType

parseExp :: String -> ParseError Char Token Exp :+: Exp
parseExp input = parse token whitespaceFilter (final exp) $ toChars input
