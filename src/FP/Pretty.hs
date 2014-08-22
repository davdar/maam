module FP.Pretty where

import FP.Core
import FP.Free
import FP.Monads

-- Setup {{{ --

newtype Color256 = Color256 { color256Raw :: Int }
  deriving (ToInteger, ToString)
instance FromInteger Color256 where
  fromInteger i | i >= 0 && i < 256 = Color256 $ fromInteger i
                | otherwise = error "Color256 values must be [0 <= n < 256] (duh!)"

data Format = Format
  { foreground :: Maybe Color256
  , background :: Maybe Color256
  , underline :: Bool
  , bold :: Bool
  }
instance Monoid Format where
  null = Format null null null null
  Format fg1 bg1 ul1 bd1 ++ Format fg2 bg2 ul2 bd2 = Format (fg1 ++ fg2) (bg1 ++ bg2) (ul1 ++ ul2) (bd1 ++ bd2)
setFG :: Color256 -> Format
setFG fg = null { foreground = Just fg }
setBG :: Color256 -> Format
setBG bg = null { background = Just bg }
setUL :: Format
setUL = null { underline = True }
setBD :: Format
setBD = null { bold = True }

data Chunk = Text String | Newline
type POut = FreeMonoidFunctor ((,) Format) Chunk
outP :: P POut
outP = P

data Layout = Flat | Break
  deriving (Eq, Ord)
data Failure = CanFail | CantFail
  deriving (Eq, Ord)
data PEnv = PEnv
  { maxColumnWidth :: Int
  , maxRibbonWidth :: Int
  , layout :: Layout
  , failure :: Failure
  , nesting :: Int
  }
maxColumnWidthL :: Lens PEnv Int
maxColumnWidthL = lens maxColumnWidth $ \ e w -> e { maxColumnWidth = w }
maxRibbonWidthL :: Lens PEnv Int
maxRibbonWidthL = lens maxRibbonWidth $ \ e w -> e { maxRibbonWidth = w }
layoutL :: Lens PEnv Layout
layoutL = lens layout $ \ e l -> e { layout = l }
failureL :: Lens PEnv Failure
failureL = lens failure $ \ e f -> e { failure = f }
nestingL :: Lens PEnv Int
nestingL = lens nesting $ \ e n -> e { nesting = n }
env0 :: PEnv
env0 = PEnv
  { maxColumnWidth = 100
  , maxRibbonWidth = 60
  , layout = Break
  , failure = CantFail
  , nesting = 0
  }

data PState = PState
  { column :: Int
  , ribbon :: Int
  }
columnL :: Lens PState Int
columnL = lens column $ \ s c -> s { column = c }
ribbonL :: Lens PState Int
ribbonL = lens ribbon $ \ s r -> s { ribbon = r }
state0 :: PState
state0 = PState
  { column = 0
  , ribbon = 0
  }

type MonadPretty m = (MonadReader PEnv m, MonadWriter POut m, MonadState PState m, MonadZero m, MonadMaybe m)
newtype PrettyT m a = PrettyT { unPrettyT :: RWST PEnv POut PState m a }
  deriving 
    ( Unit
    , Functor
    , Applicative
    , Monad
    , MonadReaderI PEnv, MonadReaderE PEnv, MonadReader PEnv
    , MonadWriterI POut, MonadWriterE POut, MonadWriter POut
    , MonadStateI PState, MonadStateE PState, MonadState PState
    , MonadRWSI PEnv POut PState, MonadRWSE PEnv POut PState, MonadRWS PEnv POut PState
    , MonadZero
    , MonadMaybeI, MonadMaybeE, MonadMaybe
    )
runPrettyT :: (Functor m) => PEnv -> PState -> PrettyT m a -> m (a, POut, PState)
runPrettyT e s = runRWST e s . unPrettyT
type Doc = PrettyT Maybe ()

execPretty0 :: Doc -> POut
execPretty0 d =
  let rM = runPrettyT env0 state0 d
  in case rM of
    Nothing -> MonoidFunctorElem $ Text "<internal pretty printing error>"
    Just ((), o, _) -> o

instance MonadUnit PrettyT where
  mtUnit = PrettyT . mtUnit
instance MonadCounit PrettyT where
  mtCounit = PrettyT . mtCounit . unPrettyT . mtMap unPrettyT
instance MonadFunctor PrettyT where
  mtMap f = PrettyT . mtMap f . unPrettyT

class Pretty a where
  pretty :: a -> Doc
  prettyParen :: a -> Doc
  prettyParen = pretty
instance Pretty Doc where
  pretty = id

-- }}} ---

-- Low Level Interface {{{ --

text :: (MonadPretty m) => String -> m ()
text o = do
  tellP outP $ unit $ Text o
  modifyL columnL $ (+) $ length o
  modifyL ribbonL $ (+) $ countNonSpace o
  f <- askL failureL
  when (f == CanFail) $ do
    cmax <- askL maxColumnWidthL
    rmax <- askL maxRibbonWidthL
    c <- getL columnL
    r <- getL ribbonL
    when (c > cmax) mzero
    when (r > rmax) mzero
  where
    countNonSpace = iter (cond isSpace id psuc) 0

space :: (MonadZero m, MonadPretty m) => Int -> m ()
space = text . otimes " "

ifFlat :: (MonadPretty m) => m a -> m a -> m a
ifFlat flatAction breakAction = do
  l <- askL layoutL
  case l of
    Flat -> flatAction
    Break -> breakAction

whenFlat :: (MonadPretty m) => m () -> m ()
whenFlat aM = ifFlat aM $ return ()

whenBreak :: (MonadPretty m) => m () -> m ()
whenBreak aM = ifFlat (return ()) aM

hardLine :: (MonadPretty m) => m ()
hardLine = do
  tellP outP $ unit $ Text "\n"
  putL columnL 0
  putL ribbonL 0

newline :: (MonadZero m, MonadPretty m) => m ()
newline = do
  n <- askL nestingL
  hardLine
  space n

flat :: (MonadPretty m) => m a -> m a
flat = localSetL layoutL Flat

canFail :: (MonadPretty m) => m a -> m a
canFail = localSetL failureL CanFail

nest :: (MonadPretty m) => Int -> m a -> m a
nest = localL nestingL . (+)

group :: (MonadMaybeI m, MonadPretty m) => m a -> m a
group aM = ifFlat aM $ (flat . canFail) aM <|> aM

align :: (MonadPretty m) => m a -> m a
align aM = do
  i <- askL nestingL
  c <- getL columnL
  nest (c - i) aM

format :: (MonadPretty m) => Format -> m a -> m a
format f aM = do
  (a, o) <- hijack aM
  tellP outP $ MFApply (f, o)
  return a

-- }}} --

-- High Level Helpers {{{

parens :: (MonadPretty m) => m () -> m ()
parens aM = do
  format punFmt $ text "("
  align aM
  format punFmt $ text ")"

app :: (MonadPretty m) => m () -> [m ()] -> m ()
app f xs = group $ do
  f
  traverseOn xs $ \ x -> nest 2 $
    ifFlat (space 1) newline >> align x

collection :: (MonadPretty m) => String -> String -> String -> [m ()] -> m ()
collection open close _ [] = pun open >> pun close
collection open close sep (x:xs) = group $ do
  pun open >> whenBreak (space 1) >> align x >> whenBreak newline
  traverseOn xs $ \ x' -> do
    pun sep >> whenBreak (space 1) >> align x' >> whenBreak newline
  pun close

-- }}}

-- Instances {{{

keyFmt :: Format
keyFmt = setFG 3 ++ setBD ++ setUL

key :: (MonadPretty m) => String -> m ()
key = format keyFmt . text

conFmt :: Format
conFmt = setFG 22 ++ setBD

con :: (MonadPretty m) => String -> m ()
con = format conFmt . text

bdrFmt :: Format
bdrFmt = setFG 6

bdr :: (MonadPretty m) => String -> m ()
bdr = format bdrFmt . text

litFmt :: Format
litFmt = setFG 1 ++ setBD

lit :: (MonadPretty m) => String -> m ()
lit = format litFmt . text

punFmt :: Format
punFmt = setFG 8

pun :: (MonadPretty m) => String -> m ()
pun = format punFmt . text

hlFmt :: Format
hlFmt = setBG 229

hl :: (MonadPretty m) => String -> m ()
hl = format hlFmt . text

headingFmt :: Format
headingFmt = setFG 5 ++ setBD ++ setUL

heading :: (MonadPretty m) => String -> m ()
heading = format headingFmt . text

instance Pretty Bool where
  pretty = lit . toString
instance Pretty Int where
  pretty = lit . toString
instance Pretty Integer where
  pretty = lit . toString
instance Pretty String where
  pretty = lit . toString
instance (Pretty a, Pretty b) => Pretty (a, b) where
  pretty (a, b) = group $ do
    pun "(" >> whenBreak (space 1) >> align (pretty a)
    whenBreak newline
    pun "," >> whenBreak (space 1) >> align (pretty b)
    whenBreak newline
    pun ")"
instance (Pretty a, Pretty b) => Pretty (a :+: b) where
  pretty (Inl a) = app (con "Inl") [prettyParen a]
  pretty (Inr b) = app (con "Inr") [prettyParen b]
  prettyParen = parens . pretty
instance (Pretty a) => Pretty [a] where
  pretty = collection "[" "]" "," . map pretty
instance (Pretty a) => Pretty (Set a) where
  pretty = collection "{" "}" "," . map pretty . toList
instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pretty = collection "{" "}" "," . map prettyMapping . toList
    where
      prettyMapping (k, v) = app (pretty k >> space 1 >> pun "=>") [pretty v]

-- }}}
