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
  _ ++ _ = undefined
instance (Pretty t) => Pretty (ParserState t) where
  pretty (ParserState s c) = P.app [P.con "ParserState", pretty s, pretty c]

parserStateP :: P t -> P (ParserState t)
parserStateP _ = P

parserStreamL :: P t -> Lens (ParserState t) [t]
parserStreamL _ = lens parserStateStream $ \ s ts -> s { parserStateStream  = ts }

parserConsumedL :: P t -> Lens (ParserState t) Int
parserConsumedL _ = lens parserStateConsumed $ \ s i -> s { parserStateConsumed  = i }

-- data ParserError t = ParserError
--   { parserErrorMsg :: Doc
--   , parserErrorState :: ParserState t
--   }
-- instance (Pretty t) => Pretty (ParserError t) where
--   pretty (ParserError m s) = P.app [P.con "ParserError", pretty m, pretty s]

-- parserErrorP :: P t -> P (ParserError t)
-- parserErrorP _ = P

-- data ParserPredicate a = ParserPredicate
--   { parserPredicateP :: a -> Bool
--   , parserPredicateDescription :: Doc
--   }

type MonadParser t m = (MonadStateE (ParserState t) m, MonadMaybeE m)

parseError :: (MonadParser t m) => P t -> Doc -> m a
parseError tP msg = do
  s <- getP $ parserStateP tP
  abort

end :: (MonadParser t m) => P t -> m ()
end tP = do
  ts <- getL $ parserStreamL tP
  case ts of
    [] -> return ()
    _:_ -> parseError tP $ P.text "expected end of input"

final :: (MonadParser t m) => P t -> m a -> m a
final tP aM = do
  a <- aM
  end tP
  return a

litP :: (MonadParser t m, Eq t) => P t -> (t -> Bool) -> Doc -> m t
litP tP p desc = do
  ts <- getL $ parserStreamL tP
  case ts of
    t:ts' | p t -> do
      putL (parserStreamL tP) ts'
      bumpL $ parserConsumedL tP
      return t
    _ -> parseError tP $ P.text "expected " ++ desc

lit :: (MonadParser t m, Eq t, Pretty t) => P t -> t -> m t
lit tP t = litP tP ((==) t) $ pretty t

word :: (MonadParser t m, Eq t, Pretty t) => P t -> [t] -> m [t]
word tP ts = 
  let wordM = mapM (lit tP) ts
  -- in catchP (parserErrorP tP) wordM $ \ _ -> 
  --   parseError tP $ P.text "expected word " ++ pretty ts
  in wordM

newtype Parser t a = Parser { unParser :: StateT (ParserState t) (ListT ID) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadMonoid
    , MonadStateI (ParserState t), MonadStateE (ParserState t), MonadState (ParserState t)
    -- , MonadErrorListE (ParserError t), MonadErrorListI (ParserError t), MonadErrorList (ParserError t)
    , MonadListE
    --, MonadErrorE (ParserError t) -- , MonadErrorI (ParserError t), MonadError (ParserError t)
    , MonadMaybeE
    )

runParserT :: [t] -> Parser t a -> [(a, ParserState t)]
runParserT ts aM = runID $ runListT $ runStateT (ParserState ts 0) $ unParser aM

-- getBestError :: [ParserError t] -> Doc
-- -- getBestError es = fst $ iterOn es (P.text "", 0) $ \ e (bestMsg, bestConsumed) ->
-- --   let consumed = parserStateConsumed $ parserErrorState e
-- --   in if consumed > bestConsumed
-- --     then (parserErrorMsg e, consumed)
-- --     else (bestMsg, bestConsumed)
-- getBestError = pretty . map (pretty . parserErrorMsg)

tokenize :: Parser c a -> [c] -> ErrorT [c] ID [a]
tokenize aM = loop 
  where
    loop [] = return []
    loop ts = do
      case runParserT ts aM of
        --[] -> throw (ts, getBestError es)
        [] -> throw ts
        x:xs -> do
          let xs' = x:xs
              maxConsumed = joins $ parserStateConsumed . snd ^$ xs'
              maxResult = filter ((==) maxConsumed . parserStateConsumed . snd) xs'
              (a, s) = whenNothing (error "how did this happen?") $ head maxResult
          cons a ^$ loop $ parserStateStream s 

parse :: (Pretty c, Pretty t) => Parser c t -> (t -> Bool) -> Parser t e -> [c] -> ErrorT ([c] :+: [t] :+: ([t], [e])) ID e
parse tp wp ep cs = do
  ts <- mapError Inl $ tokenize tp cs
  let ts' = filter (not . wp) ts
  case runParserT ts ep of
    -- ErrorListFailure es -> mapError (Inr . Inl) $ throw (ts', getBestError es)
    -- ErrorListFailure es -> mapError (Inr . Inl) $ throw ts'
    [] -> mapError (Inr . Inl) $ throw ts'
    -- ErrorListSuccess x [] -> return $ fst x
    x:[] -> return $ fst x
    -- ErrorListSuccess x (x1:xs) -> mapError (Inr . Inr) $ throw (ts', map fst $ x:x1:xs)
    x:x1:xs -> mapError (Inr . Inr) $ throw (ts', map fst $ x:x1:xs)
