module FP.Parser where

import FP.Core
import FP.Monads
import FP.DerivingPrism
import FP.Pretty (Pretty(..))
import qualified FP.Pretty as P
import FP.DerivingLens

-- TODO: factor out the LHS for infix and things so that we don't backtrack too much for (a) | (a + a) ...

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
  , parserBump  :: Bool
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

data Inf m a = Inf (m (a -> a -> a))
makePrisms ''Inf

data InfL m a = InfL (m (a -> a -> a)) | Pre (m (a -> a))
makePrisms ''InfL

data InfR m a = InfR (m (a -> a -> a)) | Post (m (a -> a))
makePrisms ''InfR

data Mix m a =  Mix (Inf m a) | MixL (InfL m a) | MixR (InfR m a)
makePrisms ''Mix

inf' :: (Monad m) => (a -> b -> a -> a) -> m b -> m (a -> a -> a)
inf' f bM = do
  b <- bM
  return $ \ aL aR -> f aL b aR

inf :: (Monad m) => (a -> b -> a -> a) -> m b -> Mix m a
inf f bM = Mix $ Inf $ inf' f bM

infl :: (Monad m) => (a -> b -> a -> a) -> m b -> Mix m a
infl f bM = MixL $ InfL $ inf' f bM

infr :: (Monad m) => (a -> b -> a -> a) -> m b -> Mix m a
infr f bM = MixR $ InfR $ inf' f bM

pre :: (Monad m) => (b -> a -> a) -> m b -> Mix m a
pre f bM = MixL $ Pre $ do
  b <- bM
  return $ \ aR -> f b aR

post :: (Monad m) => (a -> b -> a) -> m b -> Mix m a
post f bM = MixR $ Post $ do
  b <- bM
  return $ \ aL -> f aL b

closed :: (MonadParser t m) => m () -> m () -> m a -> m a
closed alM arM aM = do
  alM
  a <- botLevel aM
  arM
  return a

botLevel :: (MonadParser t m) => m a -> m a
botLevel = local $ set parserLevelL 0 . set parserBumpL False

atLevel :: (MonadParser t m) => Int -> m a -> m a
atLevel i' aM = do
  i <- askL parserLevelL
  b <- askL parserBumpL
  if (i < i') || (i == i' && not b)
    then local (set parserLevelL i' . set parserBumpL False) aM
    else mzero

bump :: (MonadParser t m) => m a -> m a
bump = local $ set parserBumpL True

buildInf :: (MonadParser t m) => m a -> [Inf m a] -> m a
buildInf aM ps = do
  aL <- bump aM
  f <- mconcat $ liftMaybeZero . coerce infL *$ ps
  aR <- bump aM
  return $ f aL aR

buildInfL :: (MonadParser t m) => m a -> [InfL m a] -> m a
buildInfL aM ps = do
  pres <- oneOrMoreList $ buildInfLPre aM ps
  aR <- bump aM
  return $ runEndo aR $ foldl (++) null $ map Endo $ pres

buildInfLPre :: (MonadParser t m) => m a -> [InfL m a] -> m (a -> a)
buildInfLPre aM ps = mconcat $ map ff ps
  where
    ff (InfL p) = do
      aL <- bump aM
      f <- p
      return $ \ aR -> f aL aR
    ff (Pre p) = p

buildInfR :: (MonadParser t m) => m a -> [InfR m a] -> m a
buildInfR aM ps = do
  aL <- bump aM
  posts <- oneOrMoreList $ buildInfRPost aM ps
  return $ runEndo aL $ foldr (++) null $ map Endo $ posts

buildInfRPost :: (MonadParser t m) => m a -> [InfR m a] -> m (a -> a)
buildInfRPost aM ps = mconcat $ map ff ps
  where
    ff (InfR p) = do
      f <- p
      aR <- bump aM
      return $ \ aL -> f aL aR
    ff (Post p) = p

buildMix :: (MonadParser t m) => m a -> [Mix m a] -> m a
buildMix aM ps = do
  let infs  = liftMaybeZero . coerce mixL  *$ ps
      infLs = liftMaybeZero . coerce mixLL *$ ps
      infRs = liftMaybeZero . coerce mixRL *$ ps
  mconcat
    [ buildInf  aM infs
    , buildInfL aM infLs
    , buildInfR aM infRs
    ]

build :: (MonadParser t m) => ([m a]) -> [(Int, [Mix m a])] -> m a
build lits lps =
  let aM = mconcat 
        [ mconcat lits
        , mconcat $ mapOn lps $ uncurry $ \ i ps -> atLevel i $ buildMix aM ps
        ]
  in aM

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
runParser ts = runID . runListT . runStateT (ParserState ts 0) . runReaderT (ParserEnv 0 False) . unParser

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
