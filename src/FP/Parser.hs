module FP.Parser where

import FP.Core
import FP.Monads
import FP.DerivingPrism
import FP.DerivingPretty
import FP.Pretty (Pretty(..))
import FP.DerivingLens

data ParserState t = ParserState 
  { parserStateStream :: [t]
  , parserStateConsumed :: Int
  }
makeLenses ''ParserState
makePrettySum ''ParserState
instance Monoid (ParserState t) where
  null = ParserState [] 0
  ParserState xs m ++ ParserState ys n = ParserState (xs ++ ys) (m + n)

class 
  ( Monad m
  , MonadZero m
  , MonadConcat m
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

between :: (MonadParser t m) => m () -> m () -> m a -> m a
between alM arM aM = do
  alM
  a <- aM
  arM
  return a

build :: (MonadParser t m) => [m a] -> Map Int [Mix m a] -> m a
build lits lps = case mapRemove lps of
  Nothing -> mconcat lits
  Just ((_i, ms), lps') -> do
    let bumped = prePostBumped ms $ build lits lps'
    buildMix bumped ms

prePostBumped :: (MonadParser t m) => [Mix m a] -> m a -> m a
prePostBumped ms aM = do
  let preM = mconcat $ liftMaybeZero . coerce (preL <.> mixLL) *$ ms
      postM = mconcat $ liftMaybeZero . coerce (postL <.> mixRL) *$ ms
  mconcat
    [ do
        ps <- oneOrMoreList preM
        a <- aM
        return $ runEndo a $ foldr (++) null $ map Endo ps
    , do
        a <- aM
        ps <- many postM
        return $ runEndo a $ foldl (++) null $ map Endo ps
    ]

buildMix :: (MonadParser t m) => m a -> [Mix m a] -> m a
buildMix aM ms = do
  a <- aM
  f <- mconcat
    [ buildMixInfL aM ms
    , buildMixInfR aM ms
    , return id
    ]
  return $ f a

buildMixInfL :: (MonadParser t m) => m a -> [Mix m a] -> m (a -> a)
buildMixInfL aM ms = do
  let inflM = mconcat $ liftMaybeZero . coerce (infLL <.> mixLL) *$ ms
  ies <- oneOrMoreList $ inflM <*> aM
  return $ \ e₁ -> runEndo e₁ $ foldl (flip (++)) null $ map Endo $ mapOn ies $ \ (f,eR) eL -> eL `f` eR

buildMixInfR :: (MonadParser t m) => m a -> [Mix m a] -> m (a -> a)
buildMixInfR aM ms = do
  let infrM = mconcat $ liftMaybeZero . coerce (infRL <.> mixRL) *$ ms
  ies <- oneOrMoreList $ infrM <*> aM
  return $ \ e₁ ->
    let (ies', eᵢ) = swizzle (e₁, ies)
    in runEndo eᵢ $ foldr (++) null $ map Endo $ mapOn ies' $ \ (eL,f) eR -> eL `f` eR
  where
    swizzle :: (a, [(b, a)]) -> ([(a, b)], a)
    swizzle (a, []) = ([], a)
    swizzle (aL, (b, a):bas) =
      let (abs, aR) = swizzle (a, bas) 
      in ((aL, b):abs, aR)

newtype Parser t a = Parser { unParser :: StateT (ParserState t) (ListT ID) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadConcat
    , MonadStateI (ParserState t), MonadStateE (ParserState t), MonadState (ParserState t)
    , MonadMaybeE
    )
instance (Eq t, Pretty t) => MonadParser t (Parser t) where

runParser :: [t] -> Parser t a -> [(a, ParserState t)]
runParser ts = runID . runListT . runStateT (ParserState ts 0) . unParser

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
makePrettySum ''ParseError

parse :: forall c t a. (Pretty c, Pretty t) => Parser c t -> (t -> Bool) -> Parser t a -> [c] -> ParseError c t a :+: a
parse tp wp ep cs = do
  ts <- mapInl LexingError $ tokenize tp cs
  let ts' = filter (not . wp) ts
  (x,xs) <- 
    maybeElimOn (coerce consL $ runParser ts' ep) (throw (ParsingError ts' :: ParseError c t a)) return
  if isL nilL xs
    then return $ fst x
    else throw (AmbiguousParse (ts', map fst $ x:xs) :: ParseError c t a)
