module FP.Parser where

import FP.Core
import FP.Monads
import FP.Pretty (Pretty(..))
import qualified FP.Pretty as P
import FP.DerivingLens

data ParserState t = ParserState 
  { parserStateStream :: [t]
  , parserStateConsumed :: Int
  }
makeLenses ''ParserState
instance Monoid (ParserState t) where
  null = ParserState [] 0
  ParserState xs m ++ ParserState ys n = ParserState (xs ++ ys) (m + n)
instance (Pretty t) => Pretty (ParserState t) where
  pretty (ParserState s c) = P.app [P.con "ParserState", pretty s, pretty c]

data ParserEnv = ParserEnv
  { parserLevel :: Int
  , parserBump  :: String
  }
makeLenses ''ParserEnv

class 
  ( Monad m
  , MonadZero m
  , MonadConcat m
  , MonadReader ParserEnv m
  , MonadStateE (ParserState t) m
  , Eq t
  , Pretty t
  ) => MonadParser t m | m -> t where

end :: forall t m. (MonadParser t m) => m ()
end = do
  ts <- getL parserStateStreamL :: m [t]
  case ts of
    [] -> return ()
    _:_ -> mzero

final :: (MonadParser t m) => m a -> m a
final aM = do
  a <- aM
  end
  return a

satisfies :: forall t m. (MonadParser t m, Eq t) => (t -> Bool) -> m t
satisfies p = do
  ts <- getL parserStateStreamL
  case ts of
    t:ts' | p t -> do
      putL parserStateStreamL ts'
      bumpL (parserStateConsumedL :: Lens (ParserState t) Int)
      return t
    _ -> mzero

lit :: (MonadParser t m) => t -> m t
lit = satisfies . (==)

word :: (MonadParser t m) => [t] -> m [t]
word ts = mapM lit ts

atLevel :: (MonadParser t m) => Int -> String -> m a -> m a
atLevel i' name aM = do
  i <- askL parserLevelL
  b <- askL parserBumpL
  if (i < i') || (i == i' && b /= name)
    then local (set parserLevelL i' . set parserBumpL name) aM
    else mzero

bump :: (MonadParser t m) => String -> m a -> m a
bump = local . set parserBumpL
  
pre' :: (MonadParser t m) => Int -> String -> m b -> m a -> m (b, [b], a)
pre' i name bM aM = atLevel i name $ do
  (y, ys) <- oneOrMore bM
  x <- aM
  return (y, ys, x)

pre :: (MonadParser t m) => Int -> String -> m b -> m a -> m ([b], a)
pre i name bM aM = (\ (y, ys, x) -> (y:ys, x)) ^$ pre' i name bM aM

pos' :: (MonadParser t m) => Int -> String -> m b -> m a -> m (a, b, [b])
pos' i name bM aM = atLevel i name $ do
  x <- aM
  (y, ys) <- oneOrMore bM
  return (x, y, ys)

pos :: (MonadParser t m) => Int-> String -> m b -> m a -> m (a, [b])
pos i name bM aM = (\ (x, y, ys) -> (x, y:ys)) ^$ pos' i name bM aM

infN :: (MonadParser t m) => Int -> String -> m b -> m a -> m (a, b, a)
infN i name bM aM = atLevel i name $ do
  x1 <- aM
  y <- bM
  x2 <- aM
  return (x1, y, x2)
  
inf' :: (MonadParser t m) => Int -> String -> m b -> m a -> m (a, b, a, [(b, a)])
inf' i name bM aM = atLevel i name $ do
  x1 <- aM
  ((y, x2), yxs) <- oneOrMore $ bM <*> aM
  return (x1, y, x2, yxs)

inf :: (MonadParser t m) => Int -> String -> m b -> m a -> m (a, [(b, a)])
inf i name bM aM = (\ (x1, y, x2, yxs) -> (x1, (y,x2) : yxs)) ^$ inf' i name bM aM

infL :: (MonadParser t m) => Int -> String -> m b -> m a -> (a -> (b, a) -> a) -> m a
infL i name bM aM f = ff ^$ inf i name bM aM
  where
    ff (x, yxs) = foldlOn yxs x $ flip f

infR :: (MonadParser t m) => Int -> String -> m b -> m a -> ((a, b) -> a -> a) -> m a
infR i name bM aM f = ff . swizzle ^$ inf i name bM aM
  where
    ff (xys, x) = foldrOn xys x f
    swizzle :: (a, [(b, a)]) -> ([(a, b)], a)
    swizzle (x, []) = ([], x)
    swizzle (x1, (y, x2) : yxs) =
      let (xys, x) = swizzle (x2, yxs)
      in ((x1, y) : xys, x)

juxt' :: (MonadParser t m) => Int -> String -> m a -> m (a, a, [a])
juxt' i name aM = atLevel i name $ do
  x1 <- aM
  (x2, xs) <- oneOrMore aM
  return (x1, x2, xs)

juxt :: (MonadParser t m) => Int -> String -> m a -> m (a, [a])
juxt i name aM = ff ^$ juxt' i name aM
  where
    ff (x1, x2, xs) = (x1, x2 : xs)

juxtL :: (MonadParser t m) => Int -> String -> m a -> (a -> a -> a) -> m a
juxtL i name aM f = ff ^$ juxt i name aM
  where
    ff (x, xs) = foldlOn xs x $ flip f

juxtR :: (MonadParser t m) => Int -> String -> m a -> (a -> a -> a) -> m a
juxtR i name aM f = ff . swizzle ^$ juxt i name aM
  where
    ff (xs, x) = foldrOn xs x f
    swizzle :: (a, [a]) -> ([a], a)
    swizzle (x, []) = ([], x)
    swizzle (x1, x2:xs) =
      let (xs',x) = swizzle (x2, xs)
      in (x1:xs', x)

closed' :: (MonadParser t m) => m b1 -> m b2 -> m a -> m (b1, a, b2)
closed' b1M b2M aM = do
  b1 <- b1M
  a <- local (set parserLevelL 0 . set parserBumpL "") aM
  b2 <- b2M
  return (b1, a, b2)

closed :: (MonadParser t m) => m b1 -> m b2 -> m a -> m a
closed b1M b2M = (\ (_, a, _) -> a) ^. closed' b1M b2M

newtype Parser t a = Parser { unParser :: ReaderT ParserEnv (StateT (ParserState t) (ListT ID)) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadConcat
    , MonadStateI (ParserState t), MonadStateE (ParserState t), MonadState (ParserState t)
    , MonadReaderI ParserEnv, MonadReaderE ParserEnv, MonadReader ParserEnv
    , MonadMaybeE
    )
instance (Eq t, Pretty t) => MonadParser t (Parser t) where

runParser :: [t] -> Parser t a -> [(a, ParserState t)]
runParser ts = runID . runListT . runStateT (ParserState ts 0) . runReaderT (ParserEnv 0 "") . unParser

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
    maybeElimOn (coerce consL $ runParser ts' ep) (throw (ParsingError ts' :: ParseError c t a)) return
  if isL nilL xs
    then return $ fst x
    else throw (AmbiguousParse (ts', map fst $ x:xs) :: ParseError c t a)
