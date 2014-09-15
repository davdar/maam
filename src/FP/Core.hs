module FP.Core 

-- Exports {{{

  ( module Prelude
  , module FP.Core
  , module GHC.Exts
  , module Data.Map
  , module Data.Char
  ) where

-- }}}

-- Imports {{{

import qualified Prelude
import Prelude 
  ( Eq(..), Ord(..)
  , (.), ($), const, flip, curry, uncurry
  , fst, snd
  , Bool(..), (||), (&&), not, otherwise
  , Char, Int, Integer, Double, Rational
  , Maybe(..)
  , undefined, seq
  , IO
  )
import Data.Text (Text)
import GHC.Exts (type Constraint)
import qualified Data.Text as Text
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Char (isSpace, isAlphaNum, isLetter, isDigit)

-- }}}

-- Precedence {{{

infixl 9 #
infixl 9 #!
infixl 9 <@>
infixl 9 *@
infixl 9 ^@
infixl 9 ^*@
infixr 9 *.
infixr 9 ^.
infixr 9 .^
infixr 9 ^^.
infixr 9 ^.:
infixr 9 ^*.
infixr 9 <.>
infixr 9 ..:
infixr 9 :.:
infixr 9 :..:

infix 7 /
infix 7 //
infixr 7 *
infixr 7 <*>
infixr 7 /\

infix 6 -
infix 6 \-\
infixr 6 +
infixr 6 ++
infixr 6 :+:
infixr 6 <+>
infixr 6 \/

infix 4 <~
infix 4 <.
infix 4 ?
infix 4 #?

infixl 1 >>=
infixl 1 >>
infixr 1 ~>

infixr 0 *$
infixr 0 ^$
infixr 0 ^*$
infixr 0 <$>
infixr 0 ^*$~

infixr 0 ~:
infixr 0 =:
infixr 0 |:

-- }}}

-------------
-- Classes --
-------------

-- Category {{{ --

class Category t where
  id :: t a a
  (<.>) :: t b c -> t a b -> t a c

-- }}} --

-- Morphism {{{

type m ~> n = forall a. m a -> n a
type t ~~> u = forall a m. t m a -> u m a

class Morphism a b where
  morph :: a -> b
class FMorphism m n where
  fmorph :: m ~> n
class FFMorphism t u where
  ffmorph :: t ~~> u

-- }}}

-- Isomorphism {{{

class (Morphism a b, Morphism b a) => Isomorphism a b where

ito :: (Isomorphism a b) => a -> b
ito = morph
ifrom :: (Isomorphism a b) => b -> a
ifrom = morph

class (FMorphism t u, FMorphism u t) => FIsomorphism t u where

fto :: (FIsomorphism t u) => t a -> u a
fto = fmorph
ffrom :: (FIsomorphism t u) => t a -> u a
ffrom = fmorph

class (FFMorphism v w, FFMorphism w v) => FFIsomorphism v w where

ffto :: (FFIsomorphism v w) => v t a -> w t a
ffto = ffmorph
fffrom :: (FFIsomorphism v w) => v t a -> w t a
fffrom = ffmorph

-- }}}

-- Monoid {{{

class Monoid a where
  null :: a
  (++) :: a -> a -> a

otimes :: (Peano n, Monoid a) => a -> n -> a
otimes a = piter (a ++) null

concat :: (CoIterable a t, Monoid a) => t -> a
concat = coiter (++) null

-- }}}

-- Conversion {{{

class ToInteger a where
  toInteger :: a -> Integer
class FromInteger a where
  fromInteger :: Integer -> a

class ToInt a where
  toInt :: a -> Int
class FromInt a where
  fromInt :: Int -> a

class ToRational a where
  toRational :: a -> Rational
class FromRational a where
  fromRational :: Rational -> a

class ToDouble a where
  toDouble :: a -> Double
class FromDouble a where
  fromDouble :: Double -> a

class FromChars a where
  fromChars :: Chars -> a
class ToChars a where
  toChars :: a -> Chars
-- for Overlaoded Strings extension
fromString :: Chars -> String
fromString = fromChars

class ToString t where
  toString :: t -> String

-- }}}

-- Arithmetic {{{ --

class Peano a where
  pzero :: a
  psuc :: a -> a
  piter :: (b -> b) -> b -> a -> b

piterOn :: (Peano a) => a -> b -> (b -> b) -> b
piterOn = mirror piter

class Additive a where
  zero :: a
  (+) :: a -> a -> a
class (Additive a) => Subtractive a where
  (-) :: a -> a -> a
class (Additive a) => Multiplicative a where
  one :: a
  (*) :: a -> a -> a
class (Multiplicative a) => Divisible a where
  (/) :: a -> a -> a
class (Multiplicative a) => TruncateDivisible a where
  (//) :: a -> a -> a

negate :: (Subtractive a) => a -> a
negate x = zero - x

inverse :: (Divisible a) => a -> a
inverse x = one / x

class (Peano a, TruncateDivisible a, FromInteger a, ToInteger a, FromInt a, ToInt a) => Integral a where
class (Peano a, Divisible a, FromInteger a, FromDouble a, ToDouble a) => Floating a where

-- }}}

-- PartialOrder {{{

data POrdering = PEQ | PLT | PGT | PUN

class PartialOrder a where
  pcompare :: a -> a -> POrdering
  pcompare x y = case (x <~ y, y <~ x) of
    (True , True ) -> PEQ
    (True , False) -> PLT
    (False, True ) -> PGT
    (False, False) -> PUN
  (<~) :: a -> a -> Bool
  x <~ y = case pcompare x y of
    PLT -> True
    PEQ -> True
    _   -> False
  (<.) :: a -> a -> Bool
  x <. y = case pcompare x y of
    PLT -> True
    _ -> False

class PartialOrderF t where
  partialOrderF :: (PartialOrder a) => W (PartialOrder (t a))

discreteOrder :: (Eq a) => a -> a -> POrdering
discreteOrder x y = if x == y then PEQ else PUN

poiter :: (PartialOrder a) => (a -> a) -> a -> a
poiter f = loop
  where
    loop x =
      let x' = f x
      in if x' <~ x then x else loop x'

-- }}}

-- Lattice {{{ --

class HasBot a where
  bot :: a
class (HasBot a) => JoinLattice a where
  (\/) :: a -> a -> a

joins :: (Iterable a t, JoinLattice a) => t -> a
joins = iter (\/) bot

collect :: (JoinLattice a, PartialOrder a) => (a -> a) -> a -> a
collect f = poiter $ \ x -> x \/ f x

collectN :: (JoinLattice a, PartialOrder a, Peano n) => n -> (a -> a) -> a -> a
collectN n f x0 = piterOn n x0 $ \ x -> x \/ f x

class MeetLattice a where
  top :: a
  (/\) :: a -> a -> a

class (JoinLattice a, MeetLattice a) => Lattice a where

-- }}} --

-- Negatable{{{ 

class Dual a where
  dual :: a -> a

-- }}}

-- Universal{{{ 

class Universal a where
instance Universal a

-- }}}

-- CProduct {{{

class (c1 a, c2 a) => (c1 ::*:: c2) a where
instance (c1 a, c2 a) => (c1 ::*:: c2) a where

-- }}}

-- CCompose {{{

class (t (u a)) => (t ::.:: u) a where
instance (t (u a)) => (t ::.:: u) a where

-- }}}

-- Iterable {{{

class Iterable a t | t -> a where
  iter :: (a -> b -> b) -> b -> t -> b

iterOn :: (Iterable a t) => t -> b -> (a -> b -> b) -> b
iterOn = mirror iter

iterFrom :: (Iterable a t) => b -> (a -> b -> b) -> t -> b
iterFrom = flip iter

traverse :: (Iterable a t, Monad m) => (a -> m ()) -> t -> m ()
traverse f = iter (\ a m -> m >> f a) $ return ()

traverseOn :: (Iterable a t, Monad m) => t -> (a -> m ()) -> m ()
traverseOn = flip traverse

exec :: (Iterable (m ()) t, Monad m) => t -> m ()
exec = traverse id

class CoIterable a t | t -> a where
  coiter :: (a -> b -> b) -> b -> t -> b

toList :: (CoIterable a t) => t -> [a]
toList = coiter (:) []

toListIter :: (Iterable a t) => t -> [a]
toListIter = iter (:) []

-- }}}

-- Buildable {{{

class Buildable a t | t -> a where
  nil :: t
  cons :: a -> t -> t

fromList :: (Buildable a t) => [a] -> t
fromList = coiter cons nil

-- }}}

-- Functorial {{{

class Functorial c t where
  functorial :: (c a) => W (c (t a))

class Bifunctorial c t where
  bifunctorial :: (c a, c b) => W (c (t a b))

bifunctorialP :: (Bifunctorial c t, c a, c b) => P c -> P t -> P a -> P b -> W (c (t a b))
bifunctorialP P P P P = bifunctorial

-- }}}

-- MapLike {{{

class (Indexed k v t, Iterable (k, v) t) => MapLike k v t | t -> k, t -> v where
  pempty :: t
  psingleton :: k -> v -> t
  punionWith :: (v -> v -> v) -> t -> t -> t
  pintersectionWith :: (v -> v -> v) -> t -> t -> t
  pmodify :: (v -> v) -> k -> t -> t
  psize :: (Integral n) => t -> n

pinsertWith :: (MapLike k v t) => (v -> v -> v) -> k -> v -> t -> t
pinsertWith f k v = punionWith f (psingleton k v)

pinsert :: (MapLike k v t) => k -> v -> t -> t
pinsert = pinsertWith $ const id

ponlyKeys :: (Iterable k t, MapLike k v u) => t -> u -> u
ponlyKeys t u = iter (\ k -> maybe id (pinsert k) $ u # k) pempty t

-- }}}

-- SetLike {{{

class (Iterable e t) => SetLike c e t | t -> e, t -> c where
  sempty :: t
  ssingleton :: (c e) => e -> t
  sunion :: t -> t -> t
  sintersection :: t -> t -> t
  (\-\) :: t -> t -> t
  (?) :: t -> e -> Bool
  ssize :: (Integral n) => t -> n

sunionMap :: (Iterable a t, SetLike c b u) => (a -> u) -> t -> u
sunionMap f = iter (sunion . f) sempty

sunionMapOn :: (Iterable a t, SetLike c b u) => t -> (a -> u) -> u
sunionMapOn = flip sunionMap

selemOf :: (SetLike c e t) => t -> e -> Bool
selemOf = (?)

-- }}}

-- VectorLike {{{

class (Indexed Int a t, Iterable a t) => VectorLike a t where
  length :: t -> Int

-- }}}

-- Indexed {{{

class Indexed i e t | t -> i, t -> e where
  (#) :: t -> i -> Maybe e
  (#!) :: t -> i -> e
  (#!) = unsafeCoerceJust .: (#)

index :: (Indexed i e t) => t -> i -> Maybe e
index = (#)

lookup :: (Indexed i e t) => i -> t -> Maybe e
lookup = flip (#)

-- }}}

-- Container {{{

class Container e t | t -> e where
  (#?) :: t -> e -> Bool

elemOf :: (Container e t) => t -> e -> Bool
elemOf = (#?)

-- }}}

-- Functor {{{

class Functor t where
  map :: (a -> b) -> t a -> t b

(^@) :: (Functor t) => (a -> b) -> t a -> t b
(^@) = map

(^$) :: (Functor t) => (a -> b) -> t a -> t b
(^$) = map

(^.) :: (Functor t) => (b -> c) -> (a -> t b) -> a -> t c
g ^. f = map g . f

(.^) :: (Functor t) => (t b -> c) -> (a -> b) -> t a -> c
g .^ f = g . map f

(^.:) :: (Functor t) => (c -> d) -> (a -> b -> t c) -> a -> b -> t d
g ^.: f = map g .: f

(^..:) :: (Functor t) => (d -> e) -> (a -> b -> c -> t d) -> a -> b -> c -> t e
g ^..: f = map g ..: f

(^^.) :: (Functor t, Functor u) => (b -> c) -> (a -> t (u b)) -> a -> (t (u c))
g ^^. f = map (map g) . f

mapOn :: (Functor t) => t a -> (a -> b) -> t b
mapOn = flip map

class FunctorM t where
  mapM :: (Monad m) => (a -> m b) -> t a -> m (t b)

(^*@) :: (FunctorM t, Monad m) => (a -> m b) -> t a -> m (t b)
(^*@) = mapM

(^*$) :: (FunctorM t, Monad m) => (a -> m b) -> t a -> m (t b)
(^*$) = mapM

(^*.) :: (FunctorM t, Monad m) => (b -> m c) -> (a -> m b) -> t a -> m (t c)
(g ^*. f) aT = mapM g *$ f ^*$ aT

mapMOn :: (FunctorM t, Monad m) => t a -> (a -> m b) -> m (t b)
mapMOn = flip mapM

sequence :: (FunctorM t, Monad m) => t (m a) -> m (t a)
sequence = mapM id

class CFunctor c t | t -> c where
  cmap :: (c a, c b) => (a -> b) -> t a -> t b

(^*$~) :: (CFunctor c t, c a, c b) => (a -> b) -> t a -> t b
(^*$~) = cmap

cmapOn :: (CFunctor c t, c a, c b) => t a -> (a -> b) -> t b
cmapOn = flip cmap

class CFunctorM c t | t -> c where
  cmapM :: (Monad m, c a, c b) => (a -> m b) -> t a -> m (t b)

csequence :: (CFunctorM c t, Monad m, c a, c (m a)) => t (m a) -> m (t a)
csequence = cmapM id

-- }}}

-- Applicative {{{

class Product t where
  (<*>) :: t a -> t b -> t (a, b)
tprod :: (Product t) => t a -> t b -> t (a, b)
tprod = (<*>)

class Applicative t where
  (<@>) :: t (a -> b) -> t a -> t b
tapply :: (Applicative t) => t (a -> b) -> t a -> t b
tapply = (<@>)

(<$>) :: (Applicative t) => t (a -> b) -> t a -> t b
(<$>) = (<@>)

-- }}}

-- Unit {{{

class Unit t where
  unit :: a -> t a

class CUnit c t | t -> c where
  cunit :: (c a) => a -> t a

-- }}}

-- Monad {{{

class Bind (m :: * -> *) where
  (>>=) :: m a -> (a -> m b) -> m b
class (Unit m, Functor m, Product m, Applicative m, Bind m) => Monad m where
class MonadFail (m :: * -> *) where
  fail :: Chars -> m a

return :: (Monad m) => a -> m a
return = unit

freturn :: (Monad m) => (a -> b) -> (a -> m b)
freturn = (.) return

(>>) :: (Bind m) => m a -> m b -> m b
aM >> bM = aM >>= const bM

extend :: (Bind m) => (a -> m b) -> (m a -> m b)
extend = flip (>>=)

void :: (Functor m) => m a -> m ()
void = map (const ())

(*@) :: (Bind m) => (a -> m b) -> (m a -> m b)
(*@) = extend

(*$) :: (Bind m) => (a -> m b) -> (m a -> m b)
(*$) = extend

(*.) :: (Bind m) => (b -> m c) -> (a -> m b) -> (a -> m c)
(g *. f) x = g *$ f x

mmap :: (Bind m, Unit m) => (a -> b) -> m a -> m b
mmap f aM = do
  a <- aM
  unit $ f a

mpair :: (Bind m, Unit m) => m a -> m b -> m (a, b)
mpair aM bM = do
  a <- aM
  b <- bM
  unit (a, b)

mapply :: (Bind m, Unit m) => m (a -> b) -> m a -> m b
mapply fM aM = do
  f <- fM
  a <- aM
  unit $ f a

mjoin :: (Bind m) => m (m a) -> m a
mjoin = extend id

when :: (Unit m) => Bool -> m () -> m ()
when True = id
when False = const $ unit ()

type CMonad c m = (CUnit c m, CFunctor c m, Applicative m, Bind m)

creturn :: (CMonad c m, c a) => a -> m a
creturn = cunit

cmmap :: (CMonad c m) => (c b) => (a -> b) -> m a -> m b
cmmap f aM =
  aM >>= \ a ->
  creturn $ f a

-- }}}

-- Monad Transformers {{{

class HigherUnit t where
  htUnit :: m ~> t m
class HigherJoin t where
  htJoin :: t (t m) ~> t m
class HigherFunctor t where
  htMap :: (m ~> n) -> t m ~> t n
class HigherIsoFunctor t where
  htIsoMap :: (m ~> n) -> (n ~> m) -> t m ~> t n

class FunctorUnit t where
  ftUnit :: (Functor m) => m ~> t m
class FunctorJoin t where
  ftJoin :: (Functor m) => t (t m) ~> t m
class FunctorFunctor t where
  ftMap :: (Functor m, Functor n) => (m ~> n) -> t m ~> t n
class FunctorIsoFunctor t where
  ftIsoMap :: (Functor m, Functor n) => (m ~> n) -> (n ~> m) -> t m ~> t n

class MonadUnit t where
  mtUnit :: (Monad m) => m ~> t m
class MonadJoin t where
  mtJoin :: (Monad m) => t (t m) ~> t m
class MonadFunctor t where
  mtMap :: (Monad m, Monad n) => (m ~> n) -> t m ~> t n
class MonadIsoFunctor t where
  mtIsoMap :: (Monad m, Monad n) => (m ~> n) -> (n ~> m) -> t m ~> t n

-- }}}

-- MonadZero {{{

class MonadZero (m :: * -> *) where
  mzero :: m a

guard :: (Unit m, MonadZero m) => Bool -> m ()
guard True = unit ()
guard False = mzero

-- }}}

-- MonadMonoid {{{

class MonadMonoid (m :: * -> *) where
  (<++>) :: m a -> m a -> m a

mconcat :: (CoIterable (m a) t, MonadZero m, MonadMonoid m) => t -> m a
mconcat = coiter (<++>) mzero

-- }}}

-- MonadPlus {{{

class MonadPlus (m :: * -> *) where
  (<+>) :: m a -> m a -> m a

msum :: (Iterable (m a) t, MonadZero m, MonadPlus m) => t -> m a
msum = iter (<+>) mzero

msumVals :: (Iterable a t, MonadZero m, Unit m, MonadPlus m) => t -> m a
msumVals = iter ((<+>) . unit) mzero

mfsum :: (MonadZero m, MonadPlus m) => [a -> m b] -> a -> m b
mfsum fs x = iter (\ f -> (<+>) $ f x) mzero fs

oneOrMore :: (Monad m, MonadZero m, MonadMonoid m) => m a -> m (a, [a])
oneOrMore aM = do
  x <- aM
  xs <- many aM
  return (x, xs)

twoOrMore :: (Monad m, MonadZero m, MonadMonoid m) => m a -> m (a, a, [a])
twoOrMore aM = do
  x1 <- aM
  (x2, xs) <- oneOrMore aM
  return (x1, x2, xs)

oneOrMoreList :: (Monad m, MonadZero m, MonadMonoid m) => m a -> m [a]
oneOrMoreList = uncurry cons ^. oneOrMore

many :: (Monad m, MonadZero m, MonadMonoid m) => m a -> m [a]
many aM = mconcat
  [ oneOrMoreList aM
  , return []
  ]

-- }}}

-- MonadMaybe {{{

newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }
class (Monad m) => MonadMaybeI m where
  maybeI :: m ~> MaybeT m
class (Monad m) => MonadMaybeE m where
  maybeE :: MaybeT m ~> m
class (MonadMaybeI m, MonadMaybeE m) => MonadMaybe m where

useMaybeM :: (MonadMaybeE m) => m (Maybe a) -> m a
useMaybeM = maybeE . MaybeT

useMaybe :: (MonadMaybeE m) => Maybe a -> m a
useMaybe = useMaybeM . return

abort :: (MonadMaybeE m) => m a
abort = useMaybe Nothing

lookMaybe :: (MonadMaybeI m) => m a -> m (Maybe a)
lookMaybe = runMaybeT . maybeI

(<|>) :: (MonadMaybeI m) => m a -> m a -> m a
aM1 <|> aM2 = do
  aM' <- lookMaybe aM1
  case aM' of
    Just a -> return a
    Nothing -> aM2

mtries :: (MonadMaybe m) => [m a] -> m a
mtries = coiter (<|>) abort

mftries :: (MonadMaybe m) => [a -> m b] -> a -> m b
mftries fs x = mtries $ map ($ x) fs

useMaybeZero :: (Unit m, MonadZero m) => Maybe a -> m a
useMaybeZero Nothing = mzero
useMaybeZero (Just x) = unit x

cuseMaybeZero :: (CUnit c m, MonadZero m, c a) => Maybe a -> m a
cuseMaybeZero Nothing = mzero
cuseMaybeZero (Just x) = cunit x

-- }}}

-- MonadError {{{

newtype ErrorT e m a = ErrorT { runErrorT :: m (e :+: a) }

class (Monad m) => MonadErrorI e m where
  errorI :: m ~> ErrorT e m
class (Monad m) => MonadErrorE e m where
  errorE :: ErrorT e m ~> m
class (MonadErrorI e m, MonadErrorE e m) => MonadError e m where

throw :: (MonadErrorE e m) => e -> m a
throw e = errorE $ ErrorT $ return $ Inl e

catch :: (MonadErrorI e m) => m a -> (e -> m a) -> m a
catch aM h = do
  aeM <- runErrorT $ errorI aM
  case aeM of
    Inl e -> h e
    Inr a -> return a

catchP :: (MonadErrorI e m) => P e -> m a -> (e -> m a) -> m a
catchP _ = catch

-- }}}

-- MonadReader {{{

newtype ReaderT r m a = ReaderT { unReaderT :: r -> m a }
runReaderT :: r -> ReaderT r m a -> m a
runReaderT = flip unReaderT

class (Monad m) => MonadReaderI r m where
  readerI :: m ~> ReaderT r m
class (Monad m) => MonadReaderE r m where
  readerE :: ReaderT r m ~> m
class (MonadReaderI r m, MonadReaderE r m) => MonadReader r m where

ask :: (MonadReaderE r m) => m r
ask = readerE $ ReaderT return

askP :: (MonadReaderE r m) => P r -> m r
askP P = ask

askL :: (MonadReaderE r m) => Lens r a -> m a
askL l = access l ^$ ask

local :: (MonadReader r m) => (r -> r) -> m a -> m a
local f aM = readerE $ ReaderT $ \ e -> runReaderT (f e) $ readerI aM

localP :: (MonadReader r m) => P r -> (r -> r) -> m a -> m a
localP P = local

localSet :: (MonadReader r m) => r -> m a -> m a
localSet = local . const

localL :: (MonadReader r m) => Lens r b -> (b -> b) -> m a -> m a
localL = local .: update

localSetL :: (MonadReader r m) => Lens r b -> b -> m a -> m a
localSetL l = localL l . const

-- }}}

-- MonadWriter {{{

newtype WriterT o m a = WriterT { runWriterT :: m (a, o) }

class (Monad m) => MonadWriterI o m where
  writerI :: m ~> WriterT o m
class (Monad m) => MonadWriterE o m where
  writerE :: WriterT o m ~> m
class (MonadWriterI o m, MonadWriterE o m) => MonadWriter o m where

tell :: (MonadWriterE o m) => o -> m ()
tell = writerE . WriterT . return . ((),)

tellP :: (MonadWriterE o m) => P o -> o -> m ()
tellP P = tell

hijack :: (MonadWriterI o m) => m a -> m (a, o)
hijack = runWriterT . writerI

-- }}}

-- MonadState {{{

newtype StateT s m a = StateT { unStateT :: s -> m (a, s) }

class (Monad m) => MonadStateI s m where
  stateI :: m ~> StateT s m
class (Monad m) => MonadStateE s m where
  stateE :: StateT s m ~> m
class (MonadStateI s m, MonadStateE s m) => MonadState s m where

get :: (MonadStateE s m) => m s
get = stateE $ StateT $ \ s -> return (s, s)

getP :: (MonadStateE s m) => P s -> m s
getP P = get

getL :: (MonadStateE s m) => Lens s a -> m a
getL l = map (access l) get

put :: (MonadStateE s m) => s -> m ()
put s = stateE $ StateT $ \ _ -> return ((), s)

putP :: (MonadStateE s m) => P s -> s -> m ()
putP P = put

putL :: (MonadStateE s m) => Lens s a -> a -> m ()
putL = modify .: set

modifyM :: (MonadStateE s m) => (s -> m s) -> m ()
modifyM f = stateE $ StateT $ \ s -> return () <*> f s

modify :: (MonadStateE s m) => (s -> s) -> m ()
modify = modifyM . freturn

modifyP :: (MonadStateE s m) => P s -> (s -> s) -> m ()
modifyP P = modify

modifyL :: (MonadStateE s m) => Lens s a -> (a -> a) -> m ()
modifyL = modify .: update

modifyLM :: (MonadStateE s m) => Lens s a -> (a -> m a) -> m ()
modifyLM = modifyM .: updateM

localStateSet :: (MonadStateI s m) => s -> m a -> m (a, s)
localStateSet s aM = unStateT (stateI aM) s

-- these have strange behavior, maybe they shouldn't be used to avoid
-- confusion...
--
-- localState :: (MonadState s m) => (s -> s) -> m a -> m (a, s)
-- localState f aM = do
--   s <- get
--   localStateSet (f s) aM
-- 
-- localStateSetP :: (MonadStateI s m) => P s -> s -> m a -> m (a, s)
-- localStateSetP P = localStateSet
-- 
-- localStateP :: (MonadState s m) => P s -> (s -> s) -> m a -> m (a, s)
-- localStateP P = localState
-- 
-- localStateL :: (MonadState s m) => Lens s b -> (b -> b) -> m a -> m (a, b)
-- localStateL l f aM = do
--   s <- get
--   let b = access l s
--   (a, s') <- localStateSet (set l (f b) s) aM
--   put $ set l b s'
--   return (a, access l s')
-- 
-- localStateSetL :: (MonadState s m) => Lens s b -> b -> m a -> m (a, b)
-- localStateSetL l = localStateL l . const

next :: (MonadStateE s m, Peano s) => m s
next = do
  i <- get
  put $ psuc i
  return i

nextL :: (MonadStateE s m, Peano a) => Lens s a -> m a
nextL l = do
  i <- getL l
  putL l $ psuc i
  return i

bumpL :: (MonadStateE s m, Peano a) => Lens s a -> m ()
bumpL l = modifyL l psuc

-- class (CMonad c m) => CMonadStateI c s m | m -> c where
--   cstateI :: (m ~>~ StateT s m) c
-- class (CMonad c m) => CMonadStateE c s m | m -> c where
--   cstateE :: (StateT s m ~>~ m) c
-- class (CMonadStateI c s m, CMonadStateE c s m) => CMonadState c s m | m -> c where

-- cget :: (CMonadStateE c s m, c s, c (s, s)) => m s
-- cget = cstateE $ StateT $ \ s -> creturn (s, s)
-- 
-- cgetP :: (CMonadStateE c s m, c s, c (s, s)) => P s -> m s
-- cgetP P = cget
-- 
-- cgetL :: (CMonadStateE c s m, c s, c (s, s), c a) => Lens s a -> m a
-- cgetL l = cmmap (access l) cget
-- 
-- cput :: (CMonadStateE c s m, c (), c ((), s)) => s -> m ()
-- cput s = cstateE $ StateT $ \ _ -> creturn ((), s)
-- 
-- cputP :: (CMonadStateE c s m, c (), c ((), s)) => P s -> s -> m ()
-- cputP P = cput
-- 
-- cputL :: (CMonadStateE c s m, c (), c ((), s)) => Lens s a -> a -> m ()
-- cputL = cmodify .: set
-- 
-- cmodify :: (CMonadStateE c s m, c (), c ((), s)) => (s -> s) -> m ()
-- cmodify f = cstateE $ StateT $ \ s -> creturn ((), f s)
-- 
-- cmodifyP :: (CMonadStateE c s m, c (), c ((), s)) => P s -> (s -> s) -> m ()
-- cmodifyP P = cmodify
-- 
-- cmodifyL :: (CMonadStateE c s m, c (), c ((), s)) => Lens s a -> (a -> a) -> m ()
-- cmodifyL = cmodify .: update

-- }}}

-- MonadRWST {{{

newtype RWST r o s m a = RWST { unRWST :: ReaderT r (WriterT o (StateT s m)) a }

class (MonadReaderI r m, MonadWriterI o m, MonadStateI s m) => MonadRWSI r o s m where
  rwsI :: m ~> RWST r o s m
class (MonadReaderE r m, MonadWriterE o m, MonadStateE s m) => MonadRWSE r o s m where
  rwsE :: RWST r o s m ~> m
class (MonadReader r m, MonadWriter o m, MonadState s m) => MonadRWS r o s m where

-- }}}

-- MonadList {{{

newtype ListT m a = ListT { runListT :: m [a] }

class (Monad m) => MonadListI m where
  listI :: m ~> ListT m
class (Monad m) => MonadListE m where
  listE :: ListT m ~> m
class (MonadListI m, MonadListE m) => MonadList m where

listAbort :: (MonadListE m) => m a
listAbort = listE $ ListT $ unit []

-- }}}

-- MonadErrorList {{{

newtype ErrorListT e m a = ErrorListT { runErrorListT :: m (ErrorList e a) }

class (Monad m) => MonadErrorListI e m where
  errorListI :: m ~> ErrorListT e m
class (Monad m) => MonadErrorListE e m where
  errorListE :: ErrorListT e m ~> m
class (MonadErrorListI e m, MonadErrorListE e m) => MonadErrorList e m where

throwErrorList :: (MonadErrorListE e m) => e -> m a
throwErrorList = errorListE . ErrorListT . unit . ErrorListFailure . unit

-- }}}

-- MonadListSet {{{

newtype ListSetT m a = ListSetT { runListSetT :: m (ListSet a) }

class (Monad m) => MonadListSetI m  where
  listSetI :: m ~> ListSetT m
class (Monad m) => MonadListSetE m where
  listSetE :: ListSetT m ~> m
class (MonadListSetI m, MonadListSetE m) => MonadListSet m where

-- }}}


-- MonadSet {{{

newtype SetT m a = SetT { runSetT :: m (Set a) }
mapSetT :: (m (Set a) -> m (Set b)) -> SetT m a -> SetT m b
mapSetT f = SetT . f . runSetT

class (CMonad Ord m) => MonadSetI m where
  setI :: m ~> SetT m
class (CMonad Ord m) => MonadSetE m where
  setE :: SetT m ~> m

-- }}}

-- MonadKon {{{

newtype KonT r m a = KonT { runKonT :: (a -> m r) -> m r }
class (Monad m) => MonadKonI r m | m -> r where
  konI :: m ~> KonT r m
class (Monad m) => MonadKonE r m | m -> r where
  konE :: KonT r m ~> m
class (MonadKonI r m, MonadKonE r m) => MonadKon r m | m -> r where

callCC :: (MonadKonE r m) => ((a -> m r) -> m r) -> m a
callCC = konE . KonT

withC :: (MonadKonI r m) => (a -> m r) -> m a -> m r
withC k aM = runKonT (konI aM) k

reset :: (MonadKon r m) => m r -> m r
reset aM = callCC $ \ k -> k *$ withC return aM

modifyC :: (MonadKon r m) => (r -> m r) -> m a -> m a
modifyC f aM = callCC $ \ k -> withC (f *. k) aM

-- }}}

-- MonadOpaqueKon {{{

newtype KFun r m a = KFun { runKFun :: a -> m r }
newtype OpaqueKonT k r m a = OpaqueKonT { runOpaqueKonT :: k r m a -> m r }
-- class (Monad m) => MonadOpaqueKonI k r m | m -> k, m -> r where
--   opaqueKonI :: m ~> OpaqueKonT k r m
-- class (Monad m) => MonadOpaqueKonE k r m | m -> k, m -> r where
--   opaqueKonE :: OpaqueKonT k r m ~> m
-- class (MonadOpaqueKonI k r m, MonadOpaqueKonE k r m) => MonadOpaqueKon k r m | m -> k, m -> r where
class (MonadKonI r m, Monad m) => MonadOpaqueKonI k r m | m -> k, m -> r where
  withOpaqueC :: k r m a -> m a -> m r
class (MonadKonE r m, Monad m) => MonadOpaqueKonE k r m | m -> k, m -> r where
  callOpaqueCC :: (k r m a -> m r) -> m a
class (MonadKon r m, MonadOpaqueKonI k r m, MonadOpaqueKonE k r m) => MonadOpaqueKon k r m | m -> k, m -> r where

-- }}}

----------
-- Data --
----------

-- Function {{{

instance Category (->) where
  id x = x
  (<.>) g f x = g (f x)
instance Functor ((->) a) where
  map = (.)
instance (HasBot b) => HasBot (a -> b) where
  bot = const bot
instance (JoinLattice b) => JoinLattice (a -> b) where
  (\/) f g x = f x \/ g x
instance (MeetLattice b) => MeetLattice (a -> b) where
  top = const top
  (/\) f g x = f x /\ g x
instance (Lattice b) => Lattice (a -> b) where

applyTo :: a -> (a -> b) -> b
applyTo = flip ($)

(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)

(..:) :: (d -> e) -> (a -> b -> c -> d) -> (a -> b -> c -> e)
(..:) = (.) . (.:)

(...:) :: (e -> f) -> (a -> b -> c -> d -> e) -> (a -> b -> c -> d -> f)
(...:) = (.) . (..:)

(....:) :: (f -> g) -> (a -> b -> c -> d -> e -> f) -> (a -> b -> c -> d -> e -> g)
(....:) = (.) . (...:)

rotateR :: (a -> b -> c -> d) -> (c -> a -> b -> d)
rotateR f c a b = f a b c

rotateL :: (a -> b -> c -> d) -> (b -> c -> a -> d)
rotateL f b c a = f a b c

mirror :: (a -> b -> c -> d) -> (c -> b -> a -> d)
mirror f c b a = f a b c

on :: (b -> b -> c) -> (a -> b) -> (a -> a -> c)
on p f x y = p (f x) (f y)

composeEndo :: [a -> a] -> a -> a
composeEndo = unEndo . concat . map Endo

-- }}}

-- Tuple {{{

instance (PartialOrder a, PartialOrder b) => PartialOrder (a, b) where
  (a1, b1) <~ (a2, b2) = (a1 <~ a2) /\ (b1 <~ b2)
instance (HasBot a, HasBot b) => HasBot (a, b) where
  bot = (bot, bot)
instance (Monoid a, Monoid b) => Monoid (a, b) where
  null = (null, null)
  (a1, b1) ++ (a2, b2) = (a1 ++ a2, b1 ++ b2)
instance (JoinLattice a, JoinLattice b) => JoinLattice (a, b) where
  (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)
instance Bifunctorial Eq (,) where
  bifunctorial = W
instance Bifunctorial Ord (,) where
  bifunctorial = W

fstL :: Lens (a, b) a
fstL = lens fst $ \ (_,b) -> (,b)

sndL :: Lens (a, b) b
sndL = lens snd $ \ (a,_) -> (a,)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

mapFstM :: (Functor m) => (a -> m c) -> (a, b) -> m (c, b)
mapFstM f (a, b) = (,b) ^$ f a

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

mapSndM :: (Functor m) => (b -> m c) -> (a, b) -> m (a, c)
mapSndM f (a, b) = (a,) ^$ f b

-- }}}

-- Bool {{{ --

instance HasBot Bool where
  bot = False
instance JoinLattice Bool where
  (\/) = (||)
instance MeetLattice Bool where
  top = True
  (/\) = (&&)
instance Dual Bool where
  dual = not
instance Monoid Bool where
  null = bot
  (++) = (\/)
instance ToString Bool where
  toString = preludeShow

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  x _ = x
ifThenElse False _ y = y

cond :: (a -> Bool) -> c -> c -> (a -> c)
cond p t f x = if p x then t else f

-- }}} --

-- Sum {{{

data a :+: b = Inl a | Inr b
  deriving (Eq, Ord)

instance Unit ((:+:) a) where
  unit = Inr
instance Functor ((:+:) a) where
  map _ (Inl a) = Inl a
  map f (Inr b) = Inr $ f b
instance Product ((:+:) a) where
  Inl a <*> _ = Inl a
  _ <*> Inl a = Inl a
  Inr b <*> Inr c = Inr (b, c)
instance Applicative ((:+:) a) where
  Inl a <@> _ = Inl a
  _ <@> Inl a = Inl a
  Inr f <@> Inr b = Inr $ f b
instance Bind ((:+:) a) where
  Inl a >>= _ = Inl a
  Inr a >>= k = k a
instance Monad ((:+:) a) where

mapLeft :: (a -> c) -> a :+: b -> c :+: b
mapLeft f (Inl a) = Inl $ f a
mapLeft _ (Inr b) = Inr b

mapRight :: (b -> c) -> a :+: b -> a :+: c
mapRight _ (Inl a) = Inl a
mapRight f (Inr b) = Inr $ f b

-- }}}

-- P {{{

data P a = P

-- }}}

-- Compose {{{

newtype (t :.: u) a = Compose { runCompose :: t (u a) }
  deriving (Eq, Ord, HasBot, JoinLattice, PartialOrder)
composeL :: Lens ((t :.: u) a) (t (u a))
composeL = isoLens runCompose Compose

mapCompose :: (t (u a) -> t (u b)) -> (t :.: u) a -> (t :.: u) b
mapCompose f = Compose . f . runCompose

mapComposeM :: (Functor m) => (t (u a) -> m (t (u b))) -> (t :.: u) a -> m ((t :.: u) b)
mapComposeM f = map Compose . f . runCompose

newtype (t :..: u) m a = Compose2 { runCompose2 :: t (u m) a }

instance (Unit t, Unit u) => Unit (t :.: u) where
  unit = Compose . unit . unit
instance (Functor t, Functor u) => Functor (t :.: u) where
  map = mapCompose . map . map
instance (CFunctor ct t, Functor u) => CFunctor (ct ::.:: u) (t :.: u) where
  cmap = mapCompose . cmap . map
instance (CFunctorM ct t, FunctorM u) => CFunctorM (ct ::.:: u) (t :.: u) where
  cmapM = mapComposeM . cmapM . mapM

-- }}}

-- Pointed {{{

data Pointed a = Top | Bot | Point a

instance HasBot (Pointed a) where
  bot = Bot
instance (Eq a) => JoinLattice (Pointed a) where
  Top     \/ _   = Top
  _       \/ Top = Top
  Bot     \/ p   = p
  p       \/ Bot = p
  Point x \/ Point y 
    | x == y = Point x
    | otherwise = Top

-- }}}

-- String {{{

type String = Text
type Chars = [Char]

instance ToChars String where
  toChars = Text.unpack
instance FromChars String where
  fromChars = Text.pack
instance Monoid String where
  null = Text.empty
  (++) = Text.append
instance (Iterable Char String) where
  iter = Text.foldl' . flip
instance (Indexed Int Char String) where
  -- O(n)
  s # i =
    if i < length s
      then Just $ Text.index s i
      else Nothing
instance VectorLike Char String where
  -- O(n)
  length = Text.length
instance ToString String where
  toString = preludeShow

error :: String -> a
error = Prelude.error . toChars 

preludeShow :: (Prelude.Show a) => a -> String
preludeShow = fromChars . Prelude.show

-- }}}

-- W {{{

data W (c :: Constraint) where
  W :: (c) => W c

with :: W c -> (c => a) -> a
with W x = x

-- }}}

-- Maybe {{{

instance Unit Maybe where
  unit = Just
instance Functor Maybe where map = mmap
instance Product Maybe where (<*>) = mpair
instance Applicative Maybe where (<@>) = mapply
instance Bind Maybe where
  Nothing >>= _ = Nothing
  Just x >>= k = k x
instance Monad Maybe where
instance MonadZero Maybe where
  mzero = Nothing
instance MonadMaybeI Maybe where
  maybeI :: Maybe ~> MaybeT Maybe
  maybeI = MaybeT . Just
instance MonadMaybeE Maybe where
  maybeE :: MaybeT Maybe ~> Maybe
  maybeE aM = case runMaybeT aM of
    Nothing -> Nothing
    Just aM' -> aM'
instance MonadMaybe Maybe where
instance Monoid (Maybe a) where
  null = Nothing
  Just x ++ _ = Just x
  Nothing ++ aM = aM

unsafeCoerceJust :: Maybe a -> a
unsafeCoerceJust (Just a) = a
unsafeCoerceJust Nothing = error "expected Just but found Nothing"

maybe :: b -> (a -> b) -> Maybe a -> b
maybe i _ Nothing = i
maybe _ f (Just a) = f a

maybeOn :: Maybe a -> b -> (a -> b) -> b
maybeOn = rotateR maybe

whenNothing :: a -> Maybe a -> a
whenNothing x Nothing = x
whenNothing _ (Just x) = x

-- }}}

-- Set {{{

data Set a where
  EmptySet :: Set a
  Set :: (Ord a) => Set.Set a -> Set a

elimSet :: b -> ((Ord a) => Set.Set a -> b) -> Set a -> b
elimSet i _ EmptySet = i
elimSet _ f (Set s) = f s

elimSetOn :: Set a -> b -> ((Ord a) => Set.Set a -> b) -> b
elimSetOn = rotateR elimSet

learnSet :: b -> ((Ord a) => b) -> Set a -> b
learnSet i f = elimSet i $ const f

learnSetOn :: Set a -> b -> ((Ord a) => b) -> b
learnSetOn = rotateR learnSet

elimSetList :: b -> ((Ord a) => [a] -> b) -> Set a -> b
elimSetList i f = elimSet i (\ s' -> f $ toList $ Set s')

elimSetListOn :: Set a -> b -> ((Ord a) => [a] -> b) -> b
elimSetListOn = rotateR elimSetList

instance Monoid (Set a) where
  null = bot
  (++) = (\/)
instance Eq (Set a) where
  s1 == s2 =
    elimSetOn s1 (elimSetOn s2 True (const False)) $ \ s1' ->
    elimSetOn s2 False $ \ s2' ->
    s1' == s2'  
instance Ord (Set a) where
  s1 <= s2 =
    elimSetOn s1 True $ \ s1' ->
    elimSetOn s2 False $ \ s2' ->
    s1' <= s2'
instance Iterable a (Set a) where
  iter f i = elimSet i $ Set.foldl (flip f) i
instance CoIterable a (Set a) where
  coiter f i = elimSet i $ Set.foldr f i
instance (Ord a) => Buildable a (Set a) where
  nil = sempty
  cons = sinsert
instance SetLike Ord a (Set a) where
  sempty = EmptySet
  ssingleton = Set . Set.singleton
  sunion s1 s2 = 
    elimSetOn s1 s2 $ \ s1' ->
    elimSetOn s2 (Set s1') $ \ s2' ->
    Set $ Set.union s1' s2'
  s1 \-\ s2 =
    elimSetOn s1 EmptySet $ \ s1' ->
    elimSetOn s2 (Set s1') $ \ s2' ->
    Set $ s1' Set.\\ s2'
  sintersection s1 s2 =
    elimSetOn s1 EmptySet $ \ s1' ->
    elimSetOn s2 EmptySet $ \ s2' ->
    Set $ Set.intersection s1' s2'
  s ? e = elimSet False (Set.member e) s
  ssize = elimSet 0 (fromInt . Set.size)
instance CUnit Ord Set where
  cunit = ssingleton
instance Bind Set where
  aM >>= k = loop $ map k $ toList aM
    where
      loop [] = EmptySet
      loop (s:xs) = (learnSetOn s id $ sunion s) $ loop xs
instance CFunctor Ord Set where
  cmap f s = elimSetOn s EmptySet $ \ s' -> Set $ Set.map f s'
instance PartialOrder (Set a) where
  s1 <~ s2 = 
    elimSetOn s1 True $ \ s1' ->
    elimSetOn s2 False $ \ s2' ->
    Set.isSubsetOf s1' s2'
instance HasBot (Set a) where
  bot = EmptySet
instance JoinLattice (Set a) where
  (\/) = sunion
instance MonadZero Set where
  mzero = null
instance MonadPlus Set where
  (<+>) = (\/)

smember :: (SetLike c a t) => a -> t -> Bool
smember = flip (?)

sinsert :: (SetLike c a t, c a) => a -> t -> t
sinsert = sunion . ssingleton

smap :: (Iterable a t, SetLike c b u, c b) => (a -> b) -> t -> u
smap f = iter (sinsert . f) sempty

useMaybeSet :: (SetLike c a t, c a) => Maybe a -> t
useMaybeSet Nothing = sempty
useMaybeSet (Just a) = ssingleton a

sset :: (Iterable a t, SetLike c a u, c a) => t -> u
sset = iter sinsert sempty

sisEmpty :: (SetLike c a t) => t -> Bool
sisEmpty = (==) (0 :: Int) . ssize

-- }}}

-- Map {{{

instance Iterable (k, v) (Map k v) where
  iter f = Map.foldlWithKey' $ \ b k v -> f (k, v) b
instance CoIterable (k, v) (Map k v) where
  coiter f = Map.foldrWithKey $ \ k v b -> f (k, v) b
instance (Ord k) => Buildable (k, v) (Map k v) where
  nil = pempty
  cons = uncurry pinsert
instance (Ord k) => Indexed k v (Map k v) where
  p # k = Map.lookup k p
instance (Ord k) => MapLike k v (Map k v) where
  pempty = Map.empty
  psingleton = Map.singleton
  punionWith = Map.unionWith
  pintersectionWith = Map.intersectionWith
  pmodify = Map.adjust
  psize = fromInteger . toInteger . Map.size
instance (Ord k, PartialOrder v) => PartialOrder (Map k v) where
  (<~) = Map.isSubmapOfBy (<~)
instance HasBot (Map k v) where
  bot = Map.empty
instance (Ord k, JoinLattice v) => JoinLattice (Map k v) where
  (\/) = punionWith (\/)

-- }}}

-- Int {{{

instance FromInteger Int where
  fromInteger = Prelude.fromIntegral
instance ToInteger Int where
  toInteger = Prelude.toInteger
instance Peano Int where
  pzero = 0
  psuc = Prelude.succ
  piter f z i =
    if i == 0 then z
    else let z' = f z in piter f z' $ i - 1
instance Additive Int where
  zero = 0
  (+) = (Prelude.+)
instance Subtractive Int where
  (-) = (Prelude.-)
instance Multiplicative Int where
  one = 1
  (*) = (Prelude.*)
instance TruncateDivisible Int where
  (//) = Prelude.div
instance ToInt Int where
  toInt = id
instance FromInt Int where
  fromInt = id
instance Integral Int where
instance ToString Int where
  toString = preludeShow
instance HasBot Int where
  bot = Prelude.minBound
instance JoinLattice Int where
  x \/ y = Prelude.max x y

-- }}}

-- Integer {{{

instance FromInteger Integer where
  fromInteger = id
instance ToInteger Integer where
  toInteger = id
instance Additive Integer where
  zero = 0
  (+) = (Prelude.+)
instance Subtractive Integer where
  (-) = (Prelude.-)
instance ToString Integer where
  toString = preludeShow

-- }}}

-- Char {{{

instance ToString Char where
  toString = preludeShow

-- }}}

-- IO {{{

instance Unit IO where
  unit = Prelude.return
instance Functor IO where
  map = mmap
instance Applicative IO where
  (<@>) = mapply
instance Product IO where
  (<*>) = mpair
instance Bind IO where
  (>>=) = (Prelude.>>=)
instance Monad IO where

print :: String -> IO ()
print = Prelude.putStrLn . toChars

-- }}}

-- Lens {{{ --

data Cursor a b = Cursor { focus :: a, construct :: a -> b }

data Lens a b = Lens { runLens :: a -> Cursor b a }

lens :: (a -> b) -> (a -> b -> a) -> Lens a b
lens getter setter = Lens $ \ s -> Cursor (getter s) (setter s)

isoLens :: (a -> b) -> (b -> a) -> Lens a b
isoLens to from = lens to $ const from

instance Category Lens where
  id = Lens $ \ a -> Cursor a id
  g <.> f = Lens $ \ a -> 
    let Cursor b ba = runLens f a
        Cursor c cb = runLens g b
    in Cursor c $ ba . cb

access :: Lens a b -> a -> b
access = focus .: runLens

update :: Lens a b -> (b -> b) -> a -> a
update l f a =
  let Cursor b ba = runLens l a
  in ba $ f b
(~:) :: Lens a b -> (b -> b) -> a -> a
(~:) = update

updateM :: (Monad m) => Lens a b -> (b -> m b) -> a -> m a
updateM l f a =
  let Cursor b ba = runLens l a
  in map ba $ f b

set :: Lens a b -> b -> a -> a
set l = update l . const
(=:) :: Lens a b -> b -> a -> a
(=:) = set

(|:) :: a -> (a -> a) -> a
(|:) = applyTo

-- }}} --

-- List {{{

instance Functorial Eq [] where functorial = W
instance Functorial Ord [] where functorial = W

instance Functor [] where
  map _ [] = []
  map f (x:xs) = f x:map f xs
instance FunctorM [] where
  mapM _ [] = return []
  mapM f (x:xs) = do
    y <- f x
    ys <- mapM f xs
    return $ y:ys
instance Iterable a [a] where
  iter _ i [] = i
  iter f i (x:xs) = let i' = f x i in i' `seq` iter f i' xs
instance CoIterable a [a] where
  coiter _ i [] = i
  coiter f i (x:xs) = f x $ coiter f i xs
instance Monoid [a] where
  null = []
  xs ++ ys = coiter (:) ys xs
instance Functorial Monoid [] where functorial = W
instance Unit [] where
  unit = (:[])
instance Bind [] where
  []     >>= _ = []
  (x:xs) >>= k = k x ++ (xs >>= k)
instance Monad [] where
instance Product [] where
  (<*>) = mpair
instance Applicative [] where
  (<@>) = mapply
instance MonadZero [] where
  mzero = []
instance MonadMonoid [] where
  (<++>) = (++)
instance (Eq a) => Container a [a] where
  xs #? y = coiter (\ x -> (||) $ x == y) False xs
instance Buildable a [a] where
  nil = []
  cons = (:)

singleton :: a -> [a]
singleton = (:[])

zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x,y):zip xs ys

unzip :: [(a, b)] -> ([a], [b])
unzip [] = ([], [])
unzip ((x,y):xys) =
  let (xs,ys) = unzip xys
  in (x:xs, y:ys)

zipSameLength :: [a] -> [b] -> Maybe [(a, b)]
zipSameLength [] [] = Just []
zipSameLength [] (_:_) = Nothing
zipSameLength (_:_) [] = Nothing
zipSameLength (x:xs) (y:ys) = do
  xys <- zipSameLength xs ys
  return $ (x, y):xys

firstN :: (Eq n, Integral n) => n -> [a] -> [a]
firstN n = recur zero
  where
    recur _ [] = []
    recur i (x:xs) | i == n = []
                   | otherwise = x:recur (psuc i) xs

intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse i0 (x0:xs0) = x0 : recur i0 xs0
  where
    recur _ [] = []
    recur i (x:xs) = i:x:recur i xs

pluck :: [a] -> [[a]] -> Maybe ([a], [[a]])
pluck [] _ = Nothing
pluck (x:xs) [] = Just ([x], [xs])
pluck (x1:xs1) (xs2:xss) = do
  (ys2, xss') <-  pluck xs2 xss
  return (x1 : ys2, xs1 : xss')

transpose :: [[a]] -> [[a]]
transpose [] = [[]]
transpose (xs:xss) =
  case pluck xs xss of
    Nothing -> []
    Just (ys, xss') -> ys : transpose xss'

setTranspose :: forall a. Set (Set a) -> Set (Set a)
setTranspose aMM = result
  where
    aML = toList aMM
    result = loop aML
    loop [] = EmptySet
    loop (s:ss) = 
      learnSetOn s (loop ss) $
      fromList $ map fromList $ transpose $ map toList aML

mapRest :: (a -> a) -> [a] -> [a]
mapRest _ [] = []
mapRest f (x:xs) = x:map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter p = coiter (\ x -> if p x then (:) x else id) []

head :: [a] -> Maybe a
head [] = Nothing
head (x:_) = Just x

tail :: [a] -> Maybe [a]
tail [] = Nothing
tail (_:xs) = Just xs

-- }}}

-- ListSet {{{

newtype ListSet a = ListSet { runListSet :: [a] }
  deriving (Monoid, Unit, Functor, Product, Applicative, Bind, Monad, Iterable a, CoIterable a)
instance HasBot (ListSet a) where
  bot = ListSet []
instance JoinLattice (ListSet a) where
  xs1 \/ xs2 = ListSet $ runListSet xs1 ++ runListSet xs2
instance MonadPlus ListSet where
  (<+>) = (\/)

-- }}}

-- ErrorList {{{

data ErrorList e a =
    ErrorListFailure [e]
  | ErrorListSuccess a [a]

instance Monoid (ErrorList e a) where
  null = ErrorListFailure []
  ErrorListFailure e1 ++ ErrorListFailure e2 = ErrorListFailure $ e1 ++ e2
  ErrorListSuccess x xs ++ ErrorListSuccess y ys = ErrorListSuccess x (xs ++ (y:ys))
  ErrorListFailure _ ++ ys = ys
  xs ++ ErrorListFailure _ = xs
instance Functorial Monoid (ErrorList e) where functorial = W
instance Unit (ErrorList e) where
  unit x = ErrorListSuccess x []
instance Functor (ErrorList e) where
  map = mmap
instance Product (ErrorList e) where
  (<*>) = mpair
instance Applicative (ErrorList e) where
  (<@>) = mapply
instance Bind (ErrorList e) where
  ErrorListFailure e >>= _ = ErrorListFailure e
  ErrorListSuccess x [] >>= k = k x
  ErrorListSuccess x (x':xs') >>= k = k x ++ (ErrorListSuccess x' xs' >>= k)
instance Monad (ErrorList e) where
instance MonadZero (ErrorList e) where
  mzero = null
instance MonadMonoid (ErrorList e) where
  (<++>) = (++)
instance CoIterable a (ErrorList e a) where
  coiter _ i (ErrorListFailure _) = i
  coiter f i (ErrorListSuccess x xs) = f x $ coiter f i xs
instance Buildable a (ErrorList e a) where
  nil = ErrorListFailure []
  cons x xs = ErrorListSuccess x $ toList xs

errorListConcat :: ErrorList e (ErrorList e a) -> ErrorList e a
errorListConcat (ErrorListFailure e) = ErrorListFailure e
errorListConcat (ErrorListSuccess x xs) = x ++ concat xs

errorListPluck :: ErrorList e a -> ErrorList e (ErrorList e a) -> [e] :+: (ErrorList e a, ErrorList e (ErrorList e a))
errorListPluck (ErrorListFailure e1) (ErrorListFailure e2) = Inl $ e1 ++ e2
errorListPluck (ErrorListFailure e1) (ErrorListSuccess _ _) = Inl e1
errorListPluck (ErrorListSuccess x xs) (ErrorListFailure _) = Inr (unit x, unit $ fromList xs)
errorListPluck (ErrorListSuccess x1 xs1) (ErrorListSuccess xs2 xss) = do
  (ys2, xss') <- errorListPluck xs2 $ fromList xss
  return (ErrorListSuccess x1 $ toList ys2, ErrorListSuccess (fromList xs1) $ toList xss')

errorListTranspose :: ErrorList e (ErrorList e a) -> ErrorList e (ErrorList e a)
errorListTranspose (ErrorListFailure e) = unit $ ErrorListFailure e
errorListTranspose (ErrorListSuccess xs xss) =
  case errorListPluck xs $ fromList xss of
    Inl e -> ErrorListFailure e
    Inr (ys, xss') -> ErrorListSuccess ys $ toList $ errorListTranspose xss'

-- }}}

-- Endo {{{

data Endo a = Endo { unEndo :: a -> a }
runEndo :: a -> Endo a -> a
runEndo = flip unEndo

instance Monoid (Endo a) where
  null = Endo id
  g ++ f = Endo $ unEndo g . unEndo f

data KleisliEndo m a = KleisliEndo { unKleisliEndo :: a -> m a }
runKleisliEndo :: a -> KleisliEndo m a -> m a
runKleisliEndo = flip unKleisliEndo

instance (Monad m) => Monoid (KleisliEndo m a) where
  null = KleisliEndo return
  g ++ f = KleisliEndo $ unKleisliEndo g *. unKleisliEndo f

-- }}}

-- Annotated {{{

data Annotated ann a = Annotated
  { annotation :: ann
  , annValue :: a
  }

-- }}}

-- Fix {{{

data Stamped a f = Stamped
  { stampedID :: a
  , stamped :: f
  }
instance (Eq a) => Eq (Stamped a f) where
  (==) = (==) `on` stampedID
instance (Ord a) => Ord (Stamped a f) where
  compare = compare `on` stampedID

newtype Fix f = Fix { runFix :: f (Fix f) }
data StampedFix a f = StampedFix
  { stampedFixID :: a
  , stampedFix :: f (StampedFix a f)
  } 
instance (Eq a) => Eq (StampedFix a f) where
  (==) = (==) `on` stampedFixID
instance (Ord a) => Ord (StampedFix a f) where
  compare = compare `on` stampedFixID

-- }}}
