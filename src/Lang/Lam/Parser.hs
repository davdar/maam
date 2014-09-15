module Lang.Lam.Parser where

import FP
import FP.Parser
import qualified FP.Pretty as P
import Lang.Lam.Syntax
import qualified Prelude as Prelude
import Lang.Lam.Instances.PrettySyntax ()

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
  pretty (Token t s) = P.app [P.con "Token", pretty t, pretty s]

charP :: P Char
charP = P

tokenP :: P Token
tokenP = P

white :: Parser Char String
white = fromChars ^$ oneOrMoreList $ litP charP isSpace $ P.text "a space"

string :: String -> Parser Char String
string = fromChars ^. word charP . toChars

numLit :: Parser Char String
numLit = fromChars ^$ oneOrMoreList $ litP charP isDigit $ P.text "a digit"

ident :: Parser Char String
ident = fromChars ^$ oneOrMoreList $ litP charP (isLetter \/ isDigit \/ (==) '-' \/ (==) '_') $ P.text "a valid identifier"

token :: Parser Char Token
token = mconcat
  [ Token White ^$ white
  , Token Key ^$ mconcat
      [ string "("
      , string ")"
      , string "let"
      , string ":="
      , string "in"
      , string "λ"
      , string "."
      , string "begin"
      , string "end"
      , string "if"
      , string "then"
      , string "else"
      , string "T"
      , string "F"
      , string "+"
      , string "*"
      , string "-"
      ]
  , Token Num ^$ numLit
  , Token Id ^$ ident
  ] 

pun :: String -> Parser Token ()
pun = void . lit tokenP . Token Key

nameExp :: Parser Token Name
nameExp = Name . tokenVal ^$ litP tokenP ((==) Id . tokenType) $ P.text "an identifier"

litExp :: Parser Token Lit
litExp = mconcat
  [ I . Prelude.read . toChars . tokenVal ^$ litP tokenP ((==) Num . tokenType) $ P.text "a number"
  , const (B True) ^$ lit tokenP $ Token Key "T"
  , const (B False) ^$ lit tokenP $ Token Key "T"
  ]

letExp :: Parser Token Exp
letExp = do
  pun "let"
  x <- nameExp
  pun ":="
  e1 <- openExp
  pun "in"
  e2 <- openExp
  return $ Fix $ Let x e1 e2

lamExp :: Parser Token Exp
lamExp = do
  pun "λ"
  x <- nameExp
  pun "."
  e <- openExp
  return $ Fix $ Lam x e

parenExp :: Parser Token Exp
parenExp = do
  pun "("
  e <- openExp
  pun ")"
  return e

appExp :: Parser Token Exp
appExp = do
  (e1, e2, es) <- twoOrMore closedExp
  return $ iter (\ a f -> Fix $ App f a) (Fix $ App e1 e2) es

openExp :: Parser Token Exp
openExp = mconcat
  [ appExp
  , closedExp
  ]

closedExp :: Parser Token Exp
closedExp = mconcat
  [ letExp
  , lamExp
  , Fix . Lit ^$ litExp
  , Fix . Var ^$ nameExp
  , parenExp
  ]

whitespaceFilter :: Token -> Bool
whitespaceFilter = (==) White . tokenType

parseLam :: String -> Doc :+: Exp
parseLam = parseExp openExp

parseExp :: Parser Token Exp -> String -> Doc :+: Exp
parseExp p input = Inl $ pretty $ parse token whitespaceFilter (final tokenP p) $ toChars input

testInput :: String
testInput = "let x := 5 in y"
