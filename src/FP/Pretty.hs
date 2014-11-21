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
  , wrap :: Bool
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
wrapL :: Lens PEnv Bool
wrapL = lens wrap $ \ e p -> e { wrap = p }
env0 :: PEnv
env0 = PEnv
  { maxColumnWidth = 100
  , maxRibbonWidth = 60
  , layout = Break
  , failure = CantFail
  , nesting = 0
  , wrap = False
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

type MonadPretty m = (MonadReader PEnv m, MonadWriter POut m, MonadState PState m, MonadMaybe m)
-- }}} ---

-- Low Level Interface {{{ --

text :: (MonadPretty m) => String -> m ()
text o = do
  tellP outP $ unit $ Text o
  modifyL columnL $ (+) $ size o
  modifyL ribbonL $ (+) $ countNonSpace o
  f <- askL failureL
  when (f == CanFail) $ do
    cmax <- askL maxColumnWidthL
    rmax <- askL maxRibbonWidthL
    c <- getL columnL
    r <- getL ribbonL
    when (c > cmax) abort
    when (r > rmax) abort
  where
    countNonSpace = iter (cond isSpace id suc) 0

space :: (MonadPretty m) => Int -> m ()
space = text . flip iterateAppend " "

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

mustBreak :: (MonadPretty m) => m () -> m ()
mustBreak = (>>) $ whenFlat abort

hardLine :: (MonadPretty m) => m ()
hardLine = do
  tellP outP $ unit $ Text "\n"
  putL columnL 0
  putL ribbonL 0

newline :: (MonadPretty m) => m ()
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

hsep :: (MonadPretty m) => [m ()] -> m ()
hsep = exec . intersperse (space 1)

vsep :: (MonadPretty m) => [m ()] -> m ()
vsep = exec . intersperse newline

hvsep :: (MonadPretty m) => [m ()] -> m ()
hvsep = group . exec . intersperse (ifFlat (space 1) newline)

hsepTight :: (MonadPretty m) => [m ()] -> m ()
hsepTight = exec . intersperse (ifFlat (return ()) (space 1))

hvsepTight :: (MonadPretty m) => [m ()] -> m ()
hvsepTight = group . exec . intersperse (ifFlat (return ()) newline)

parens :: (MonadPretty m) => m () -> m ()
parens aM = do
  format punFmt $ text "("
  align aM
  format punFmt $ text ")"

wrapped :: (MonadPretty m) => m () -> m ()
wrapped = localSetL wrapL True

unwrapped :: (MonadPretty m) => m () -> m ()
unwrapped = localSetL wrapL False

parensIfWrapped :: (MonadPretty m) => m () -> m ()
parensIfWrapped aM = do
  w <- askL wrapL
  if w then parens $ unwrapped aM else unwrapped aM

app :: (MonadPretty m) => [m ()] -> m ()
app = align . parensIfWrapped . wrapped . hvsep .^ align

collection :: (MonadPretty m) => String -> String -> String -> [m ()] -> m ()
collection open close _ [] = pun open >> pun close
collection open close sep (x:xs) = group $ unwrapped $ hvsepTight $ concat
  [ return $ hsepTight [pun open, align x]
  , mapOn xs $ \ x' -> hsepTight [pun sep, align x']
  , return $ pun close
  ]

keyPunFmt :: Format
keyPunFmt = setFG 3 ++ setBD

keyPun :: (MonadPretty m) => String -> m ()
keyPun = format keyPunFmt . text

keyFmt :: Format
keyFmt = keyPunFmt ++ setUL

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
litFmt = setFG 1 -- ++ setBD

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

-- }}}

-- DocM {{{

newtype DocM a = DocM { unDocM :: RWST PEnv POut PState Maybe a }
  deriving 
    ( Unit
    , Functor
    , Product
    , Applicative
    , Bind
    , Monad
    , MonadReaderI PEnv, MonadReaderE PEnv, MonadReader PEnv
    , MonadWriterI POut, MonadWriterE POut, MonadWriter POut
    , MonadStateI PState, MonadStateE PState, MonadState PState
    , MonadMaybeI, MonadMaybeE, MonadMaybe
    )
runDocM :: PEnv -> PState -> DocM a -> Maybe (a, POut, PState)
runDocM e s = runRWST e s . unDocM

execDoc :: Doc -> POut
execDoc d =
  let rM = runDocM env0 state0 d
  in case rM of
    Nothing -> MonoidFunctorElem $ Text "<internal pretty printing error>"
    Just ((), o, _) -> o

type Doc = DocM ()

instance Monoid Doc where
  null = abort
  (++) = (>>)

class Pretty a where
  pretty :: a -> Doc
instance Pretty Doc where
  pretty = id

-- }}}

-- No Format {{{

formatChunk :: Chunk -> String
formatChunk (Text s) = s
formatChunk Newline = "\n"

noFormatOut :: POut -> String
noFormatOut (MonoidFunctorElem o) = formatChunk o
noFormatOut MFNull = ""
noFormatOut (o1 :+++: o2) = noFormatOut o1 ++ noFormatOut o2
noFormatOut (MFApply (_, o)) = noFormatOut o

ptoString :: (Pretty a) => a -> String
ptoString = noFormatOut . execDoc . pretty

-- }}}

-- Instances {{{

instance Pretty Bool where
  pretty = con . toString
instance Pretty Int where
  pretty = lit . toString
instance Pretty Integer where
  pretty = lit . toString
instance Pretty Char where
  pretty = lit . toString
instance Pretty String where
  pretty = lit . toString
instance Pretty () where
  pretty () = con "()"
instance (Pretty a, Pretty b) => Pretty (a, b) where
  pretty (a, b) = collection "(" ")" "," [pretty a, pretty b]
instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
  pretty (a, b, c) = collection "(" ")" "," [pretty a, pretty b, pretty c]
instance Bifunctorial Pretty (,) where
  bifunctorial = W
instance (Pretty a, Pretty b) => Pretty (a :+: b) where
  pretty (Inl a) = app [con "Inl", pretty a]
  pretty (Inr b) = app [con "Inr", pretty b]
instance (Pretty a) => Pretty [a] where
  pretty = collection "[" "]" "," . map pretty
instance Functorial Pretty [] where functorial = W
instance (Pretty a) => Pretty (Set a) where
  pretty = collection "{" "}" "," . map pretty . fromSet
instance (Pretty k, Pretty v) => Pretty (Map k v) where
  pretty = collection "{" "}" "," . map prettyMapping . fromMap
    where
      prettyMapping (k, v) = nest 2 $ hvsep [hsep [pretty k, pun "=>"], pretty v]

instance (Functorial Pretty f) => Pretty (Fix f) where
  pretty (Fix f) =
    with (functorial :: W (Pretty (f (Fix f)))) $
    pretty f
instance (Pretty a, Pretty f) => Pretty (Stamped a f) where
  pretty (Stamped a f) = parensIfWrapped $ exec [pretty a, pun ":", pretty f]
instance (Pretty a, Functorial Pretty f) => Pretty (StampedFix a f) where
  pretty (StampedFix a f) = 
    with (functorial :: W (Pretty (f (StampedFix a f)))) $ parensIfWrapped $
    exec [pretty a, pun ":", pretty f]

instance (Pretty a) => Pretty (ID a) where
  --pretty (ID a) = app [con "ID", pretty a]
  pretty (ID a) = pretty a
instance Functorial Pretty ID where
  functorial = W

instance (Functorial Pretty m, Pretty e, Pretty a) => Pretty (ErrorT e m a) where
  pretty (ErrorT aM) =
    with (functorial :: W (Pretty (m (e :+: a)))) $
    -- app [con "ErrorT", pretty aM]
    pretty aM

instance (Functorial Pretty m, Pretty a) => Pretty (ListT m a) where
  pretty (ListT aM) =
    with (functorial :: W (Pretty (m [a]))) $
    --app [con "ListT", pretty aM]
    pretty aM
    
-- }}}
