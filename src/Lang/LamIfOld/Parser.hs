module Lang.LamIf.Parser where

import FP
import FP.Parser
import qualified FP.Pretty as P
import Lang.LamIf.Syntax
import Lang.LamIf.Pretty ()
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

-- Lexing

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
      , "->"
      , "begin"
      , "end"
      , "if"
      , "then"
      , "else"
      , "T"
      , "F"
      , "+"
      , "-"
      , ">="
      , "<"
      , ">"
      , ","
      , "fst"
      , "snd"
      ]
  , Token Num ^$ numLit
  , Token Id ^$ ident
  ] 

-- Parsing

key :: String -> Parser Token ()
key = void . lit . Token Key

litExp :: Parser Token Lit
litExp = mconcat
  [ I . Prelude.read . toChars . tokenVal ^$ satisfies ((==) Num . tokenType)
  , const (B True) ^$ lit $ Token Key "T"
  , const (B False) ^$ lit $ Token Key "F"
  ]

nameExp :: Parser Token RawName
nameExp = RawName . tokenVal ^$ satisfies ((==) Id . tokenType)

letExp :: Mix (Parser Token) RawExp
letExp = pre (\ (x, e1) e2 -> Fix $ Let x e1 e2) $ do
  key "let"
  x <- nameExp
  key ":="
  e1 <- exp
  key "in"
  return (x, e1)

lamExp :: Mix (Parser Token) RawExp
lamExp = pre (Fix .: Lam) $ do
  key "lam"
  x <- nameExp
  key "->"
  return x

ifExp :: Mix (Parser Token) RawExp
ifExp = pre (\ (e1, e2) e3 -> Fix $ If e1 e2 e3) $ do
  key "if"
  e1 <- exp
  key "then"
  e2 <- exp
  key "else"
  return (e1, e2)

appExp :: Mix (Parser Token) RawExp
appExp = infl (\ e1 () e2 -> Fix $ App e1 e2) (return ())

tupExp :: Parser Token (RawExp, RawExp)
tupExp = do
  key "<"
  e1 <- exp
  key ","
  e2 <- exp
  key ">"
  return (e1, e2)

fstExp :: Mix (Parser Token) RawExp
fstExp = pre (\ () e -> Fix $ Pi1 e) $ void $ key "fst"

sndExp :: Mix (Parser Token) RawExp
sndExp = pre (\ () e -> Fix $ Pi2 e) $ void $ key "snd"

exp :: Parser Token RawExp
exp = buildMix lits $ fromList mixes
  where
    lits = 
      [ Fix . Lit ^$ litExp
      , Fix . Var ^$ nameExp
      , between (key "(") (key ")") exp
      , Fix . uncurry Tup ^$ tupExp
      ]
    mixes =
      [ ( toi $ 0   , [ letExp 
                , lamExp 
                , ifExp 
                ] )
      , ( toi $ 40  , [ inf (Fix ..: flip Prim) $ key ">=" >> return (LBinOp GTE $ toi 40) ] )
      , ( toi $ 50  , [ infr (Fix ..: flip Prim) $ key "+"  >> return (LBinOp Add $ toi 50) 
                , infr (Fix ..: flip Prim) $ key "-"  >> return (LBinOp Sub $ toi 50) 
                ] )
      , ( toi $ 100 , [ fstExp, sndExp, appExp ] )
      ]

testp0 :: String
testp0 = "lam x . if x then let x := 4 in x y z else w (x y) (x + y + z)"

testp1 :: String
testp1 = "(lam x . x) ((lam x . x) (lam x . x))"

par :: String -> LexParseError Char Token RawExp :+: RawExp
par = lexParseFinal token whitespaceFilter p . toChars
  where
    p :: Parser Token RawExp
    p = do
      e <- pe
      ies <- oneOrMoreList $ key "+" <*> pe
      return $ foldlOn ies e $ \ e1 ((), e2) ->
        Fix $ Prim (LBinOp Add $ toi 50) e1 e2
    pe :: Parser Token RawExp
    pe = Fix . Lit ^$ litExp

-- }}}

whitespaceFilter :: Token -> Bool
whitespaceFilter = (==) White . tokenType

parseExp :: String -> LexParseError Char Token RawExp :+: RawExp
parseExp = lexParseFinal token whitespaceFilter (final exp) . toChars

parseFile :: String -> IO RawExp
parseFile fn = do
  s <- readFile fn
  case parseExp s of
    Inl e -> do
      pprint e
      error ""
    Inr e -> return e
