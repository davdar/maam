module FP.Parser where

import FP.Core
import FP.Monads
import FP.Pretty (Pretty(..), Doc)
import qualified FP.Pretty as P

data ParserState t = ParserState 
  { parserStateStream :: [t]
  , parserStateConsumed :: Int
  }
instance Monoid (ParserState t) where
  null = ParserState [] 0
  ParserState xs m ++ ParserState ys n = ParserState (xs ++ ys) (m + n)
instance (Pretty t) => Pretty (ParserState t) where
  pretty (ParserState s c) = P.app [P.con "ParserState", pretty s, pretty c]

parserStreamL :: Lens (ParserState t) [t]
parserStreamL = lens parserStateStream $ \ s ts -> s { parserStateStream  = ts }

parserConsumedL :: Lens (ParserState t) Int
parserConsumedL = lens parserStateConsumed $ \ s i -> s { parserStateConsumed  = i }

class (MonadStateE (ParserState t) m, MonadZero m) => MonadParser t m | m -> t where

parseError :: (MonadParser t m) => Doc -> m a
parseError _msg = do
  mzero

end :: forall t m. (MonadParser t m) => m ()
end = do
  ts <- getL parserStreamL :: m [t]
  case ts of
    [] -> return ()
    _:_ -> parseError $ P.text "expected end of input"

final :: (MonadParser t m) => m a -> m a
final aM = do
  a <- aM
  end
  return a

satisfies :: forall t m. (MonadParser t m, Eq t) => (t -> Bool) -> Doc -> m t
satisfies p desc = do
  ts <- getL parserStreamL
  case ts of
    t:ts' | p t -> do
      putL parserStreamL ts'
      bumpL (parserConsumedL :: Lens (ParserState t) Int)
      return t
    _ -> parseError $ P.text "expected " ++ desc

lit :: (MonadParser t m, Eq t, Pretty t) => t -> m t
lit t = satisfies ((==) t) $ pretty t

word :: (MonadParser t m, Eq t, Pretty t) => [t] -> m [t]
word ts = mapM lit ts

newtype Parser t a = Parser { unParser :: StateT (ParserState t) (ListT ID) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadConcat
    , MonadStateI (ParserState t), MonadStateE (ParserState t), MonadState (ParserState t)
    , MonadListE
    , MonadMaybeE
    )
instance MonadParser t (Parser t) where

runParser :: [t] -> Parser t a -> [(a, ParserState t)]
runParser ts aM = runID $ runListT $ runStateT (ParserState ts 0) $ unParser aM

tokenize :: Parser c a -> [c] -> [c] :+: [a]
tokenize aM = loop 
  where
    loop [] = return []
    loop ts = do
      case runParser ts aM of
        [] -> throw ts
        x:xs -> do
          let (a, s) = findMax (parserStateConsumed . snd) x xs
          (a :) ^$ loop $ parserStateStream s 

data ParseError c t a = 
    LexingError [c] 
  | ParsingError [t]
  | AmbiguousParse ([t], [a])

instance (Pretty c, Pretty t, Pretty a) => Pretty (ParseError c t a) where
  pretty (LexingError cs) = P.app [P.con "LexingError", pretty cs]
  pretty (ParsingError ts) = P.app [P.con "ParsingError", pretty ts]
  pretty (AmbiguousParse tsas) = P.app [P.con "AmbiguousParse", pretty tsas]

parse :: forall c t a. (Pretty c, Pretty t) => Parser c t -> (t -> Bool) -> Parser t a -> [c] -> ParseError c t a :+: a
parse tp wp ep cs = do
  ts <- mapInl LexingError $ tokenize tp cs
  let ts' = filter (not . wp) ts
  (x,xs) <- 
    maybeElimOn (coerce consL $ runParser ts ep) (throw (ParsingError ts' :: ParseError c t a)) return
  if isL nilL xs
    then return $ fst x
    else throw (AmbiguousParse (ts', map fst $ x:xs) :: ParseError c t a)
