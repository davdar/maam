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
  ) => MonadParser t m | m -> t where

end :: (MonadParser t m) => m ()
end = do
  ts <- getL parserStateStreamL
  case ts of
    [] -> return ()
    _:_ -> mzero

final :: (MonadParser t m) => m a -> m a
final aM = do
  a <- aM
  end
  return a

satisfies :: (MonadParser t m) => (t -> Bool) -> m t
satisfies p = do
  ts <- getL parserStateStreamL
  case ts of
    t:ts' | p t -> do
      putL parserStateStreamL ts'
      bumpL parserStateConsumedL
      return t
    _ -> mzero

pluck :: (MonadParser t m) => m t
pluck = satisfies $ const True

lit :: (MonadParser t m, Eq t) => t -> m t
lit = satisfies . (==)

word :: (MonadParser t m, Eq t) => [t] -> m [t]
word ts = mapM lit ts

string :: (MonadParser Char m) => String -> m String
string = fromChars ^. word . toChars

newtype Parser t a = Parser { unParser :: StateT (ParserState t) (ListT ID) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadConcat
    , MonadStateI (ParserState t), MonadStateE (ParserState t), MonadState (ParserState t)
    )
instance MonadParser t (Parser t) where

runParser :: [t] -> Parser t a -> [(a, ParserState t)]
runParser ts = unID . unListT . runStateT (ParserState ts 0) . unParser

data ParseError t a =
    ParsingError
  | AmbiguousParse [a]
makePrettySum ''ParseError

parseFinal :: Parser t a -> [t] -> ParseError t a :+: a
parseFinal p ts = case map fst $ runParser ts $ final p of
  [] -> Inl ParsingError
  [x] -> Inr x
  xs -> Inl $ AmbiguousParse xs

parseFinalOn :: [t] -> Parser t a -> ParseError t a :+: a
parseFinalOn = flip parseFinal

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

data LexParseError c t a = 
    LexingError [c] 
  | LexParsingError [t]
  | LexAmbiguousParse ([t], [a])
makePrettySum ''LexParseError

lexParseFinal :: forall c t a. (Pretty c, Pretty t) => Parser c t -> (t -> Bool) -> Parser t a -> [c] -> LexParseError c t a :+: a
lexParseFinal tp wp ep cs = do
  ts <- mapInl LexingError $ tokenize tp cs
  let ts' = filter (not . wp) ts
  (x,xs) <- 
    elimMaybeOn (coerce consL $ runParser ts' ep) (throw (LexParsingError ts' :: LexParseError c t a)) return
  if isL nilL xs
    then return $ fst x
    else throw (LexAmbiguousParse (ts', map fst $ x:xs) :: LexParseError c t a)

-- Mixfix

data Mix m a = 
    Pre  (m (a -> a))
  | Post (m (a -> a))
  | Inf  (m (a -> a -> a))
  | InfL (m (a -> a -> a))
  | InfR (m (a -> a -> a))
makePrisms ''Mix

data Level m a = Level
  { levelPre :: m (a -> a)
  , levelPost :: m (a -> a)
  , levelInf :: m (a -> a -> a)
  , levelInfL :: m (a -> a -> a)
  , levelInfR :: m (a -> a -> a)
  }

splitMixes :: (MonadParser t m) => [Mix m a] -> Level m a
splitMixes ms = Level
  { levelPre = mconcat $ liftMaybeZero . coerce preL *$ ms
  , levelPost = mconcat $ liftMaybeZero . coerce postL *$ ms
  , levelInf = mconcat $ liftMaybeZero . coerce infL *$ ms
  , levelInfL = mconcat $ liftMaybeZero . coerce infLL *$ ms
  , levelInfR = mconcat $ liftMaybeZero . coerce infRL *$ ms
  }

pre :: (Monad m) => (b -> a -> a) -> m b -> Mix m a
pre f bM = Pre $ do
  b <- bM
  return $ \ aR -> f b aR

post :: (Monad m) => (a -> b -> a) -> m b -> Mix m a
post f bM = Post $ do
  b <- bM
  return $ \ aL -> f aL b

inf' :: (Monad m) => (a -> b -> a -> a) -> m b -> m (a -> a -> a)
inf' f bM = do
  b <- bM
  return $ \ aL aR -> f aL b aR

inf :: (Monad m) => (a -> b -> a -> a) -> m b -> Mix m a
inf f bM = Inf $ inf' f bM

infl :: (Monad m) => (a -> b -> a -> a) -> m b -> Mix m a
infl f bM = InfL $ inf' f bM

infr :: (Monad m) => (a -> b -> a -> a) -> m b -> Mix m a
infr f bM = InfR $ inf' f bM

between :: (MonadParser t m) => m () -> m () -> m a -> m a
between alM arM aM = do
  alM
  a <- aM
  arM
  return a

build :: (MonadParser t m) => [m a] -> Map Int [Mix m a] -> m a
build lits lps = case mapRemove lps of
  Nothing -> mconcat lits
  Just ((_i, ms), lps') -> buildMix (build lits lps') $ splitMixes ms

buildMix :: (MonadParser t m) => m a -> Level m a -> m a
buildMix aM l = mconcat
  [ buildMixPre aM $ levelPre l
  , do
      a <- aM
      f <- mconcat
        [ buildMixPost    $ levelPost l
        , buildMixInf  aM $ levelInf  l
        , buildMixInfL aM $ levelInfL l
        , buildMixInfR aM $ levelInfR l
        , return id
        ]
      return $ f a
  ]

buildMixPre :: (MonadParser t m) => m a -> m (a -> a) -> m a
buildMixPre aM preM = do
  ps <- oneOrMoreList preM
  a <- aM
  return $ foldr (.) id ps a

buildMixPost :: (MonadParser t m) => m (a -> a) -> m (a -> a)
buildMixPost postM = do
  ps <- oneOrMoreList postM
  return $ foldl (.) id ps

buildMixInf :: (MonadParser t m) => m a -> m (a -> a -> a) -> m (a -> a)
buildMixInf aM infM = do
  p <- infM
  a2 <- aM
  return $ \ a1 -> p a1 a2

buildMixInfL :: (MonadParser t m) => m a -> m (a -> a -> a) -> m (a -> a)
buildMixInfL aM infLM = do
  ies <- map (\ (f, eR) eL -> eL `f` eR) ^$ oneOrMoreList $ infLM <*> aM
  return $ foldl (flip (.)) id ies

buildMixInfR :: (MonadParser t m) => m a -> m (a -> a -> a) -> m (a -> a)
buildMixInfR aM infRM = do
  ies <- oneOrMoreList $ infRM <*> aM
  return $ \ a1 ->
    let (ies', an) = swizzle (a1, ies)
        ies'' = map (\ (eL, f) eR -> eL `f` eR) ies'
    in foldr (.) id ies'' an
  where
    swizzle :: (a, [(b, a)]) -> ([(a, b)], a)
    swizzle (a, []) = ([], a)
    swizzle (aL, (b, a):bas) =
      let (abs, aR) = swizzle (a, bas) 
      in ((aL, b):abs, aR)

