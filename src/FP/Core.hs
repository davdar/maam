module FP.Core 

-- Exports {{{

  ( module Prelude
  , module FP.Core
  , module GHC.Exts
  , module Data.Set
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
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Char (isSpace)

-- }}}

-- Precedence {{{

infixl 9 #
infixl 9 #!
infixl 9 <@>
infixr 9 <.>
infixr 9 *.
infixr 9 *.~
infixr 9 .:
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

infixl 1 >>=
infixl 1 >>=~
infixl 1 >>
infixl 1 >>~
infixr 1 ~>

infixr 0 *$
infixr 0 *$~
infixr 0 <$>
infixr 0 <$~>
infixr 0 <*$>



-- }}}

-------------
-- Classes --
-------------

-- Category {{{ --

class Category t where
  id :: t a a
  (<.>) :: t b c -> t a b -> t a c

-- }}} --

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

class (Peano a, TruncateDivisible a, FromInteger a, ToInteger a) => Integral a where
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

collect :: (JoinLattice a, PartialOrder a) =>  (a -> a) -> a -> a
collect f = poiter $ \ x -> x \/ f x

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

-- Iterable {{{

class Iterable a t | t -> a where
  iter :: (a -> b -> b) -> b -> t -> b

iterOn :: (Iterable a t) => t -> b -> (a -> b -> b) -> b
iterOn = mirror iter

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
ponlyKeys t u = iter (\ k -> maybe (pinsert k) id $ u # k) pempty t

-- }}}

-- SetLike {{{

class (Iterable e t) => SetLike e t | t -> e where
  sempty :: t
  ssingleton :: e -> t
  sunion :: t -> t -> t
  sintersection :: t -> t -> t
  (\-\) :: t -> t -> t
  (?) :: t -> e -> Bool
  ssize :: (Integral n) => t -> n

sunionMap :: (Iterable a t, SetLike b u) => (a -> u) -> t -> u
sunionMap f = iter (sunion . f) sempty

sunionMapOn :: (Iterable a t, SetLike b u) => t -> (a -> u) -> u
sunionMapOn = flip sunionMap

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

-- Functor {{{

class Functor t where
  map :: (a -> b) -> t a -> t b

(<$>) :: (Functor t) => (a -> b) -> t a -> t b
(<$>) = map

class FunctorM t where
  mapM :: (Monad m) => (a -> m b) -> t a -> m (t b)

(<*$>) :: (FunctorM t, Monad m) => (a -> m b) -> t a -> m (t b)
(<*$>) = mapM

mapMOn :: (FunctorM t, Monad m) => t a -> (a -> m b) -> m (t b)
mapMOn = flip mapM

sequence :: (FunctorM t, Monad m) => t (m a) -> m (t a)
sequence = mapM id

class CFunctor c t | t -> c where
  cmap :: (c a, c b) => (a -> b) -> t a -> t b

(<$~>) :: (CFunctor c t, c a, c b) => (a -> b) -> t a -> t b
(<$~>) = cmap

-- }}}

-- Applicative {{{

class (Unit t, Functor t) => Applicative t where
  (<*>) :: t a -> t b -> t (a, b)
  aT <*> bT = unit (,) <@> aT <@> bT
  (<@>) :: t (a -> b) -> t a -> t b
  fT <@> aT = map (uncurry ($)) $ fT <*> aT

-- }}}

-- Unit {{{

class Unit t where
  unit :: a -> t a

class CUnit c t | t -> c where
  cunit :: (c a) => a -> t a

-- }}}

-- Monad {{{

class (Functor m, Applicative m) => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b
class (Monad m) => MonadFail m where
  fail :: Chars -> m a

return :: (Monad m) => a -> m a
return = unit

(>>) :: (Monad m) => m a -> m b -> m b
aM >> bM = aM >>= const bM

extend :: (Monad m) => (a -> m b) -> (m a -> m b)
extend = flip (>>=)

(*$) :: (Monad m) => (a -> m b) -> (m a -> m b)
(*$) = extend

(*.) :: (Monad m) => (b -> m c) -> (a -> m b) -> (a -> m c)
(g *. f) x = g *$ f x

mmap :: (Monad m) => (a -> b) -> m a -> m b
mmap f aM = do
  a <- aM
  return $ f a

mpair :: (Monad m) => m a -> m b -> m (a, b)
mpair aM bM = do
  a <- aM
  b <- bM
  return (a, b)

mapply :: (Monad m) => m (a -> b) -> m a -> m b
mapply fM aM = do
  f <- fM
  a <- aM
  return $ f a

mjoin :: (Monad m) => m (m a) -> m a
mjoin = extend id

when :: (Monad m) => Bool -> m () -> m ()
when True = id
when False = const $ return ()

class (CUnit c m) => CMonad c m | m -> c where
  (>>=~) :: (c a, c b) => m a -> (a -> m b) -> m b

creturn :: (CMonad c m, c a) => a -> m a
creturn = cunit

(>>~) :: (CMonad c m, c a, c b) => m a -> m b -> m b
aM >>~ bM = aM >>=~ \ _ -> bM

cextend :: (CMonad c m, c a, c b) => (a -> m b) -> (m a -> m b)
cextend = flip (>>=~)

(*$~) :: (CMonad c m, c a, c b) => (a -> m b) -> (m a -> m b)
(*$~) = cextend

(*.~) :: (CMonad c m, c a, c b, c d) => (b -> m d) -> (a -> m b) -> (a -> m d)
(g *.~ f) x = g *$~ f x

cmmap :: (CMonad c m) => (c a, c b) => (a -> b) -> m a -> m b
cmmap f aM =
  aM >>=~ \ a ->
  creturn $ f a

-- }}}

-- Monad Transformers {{{

type m ~> n = forall (a :: *). m a -> n a
type (m ~>~ n) c = forall (a :: *). (c a) => m a -> n a

class MonadUnit t where
  mtUnit :: (Functor m) => m ~> t m
-- *not* join
class MonadCounit t where
  mtCounit :: (Functor m) => t (t m) ~> t m

class MonadFunctor t where
  mtMap :: (m ~> n) -> t m ~> t n

class MonadIsoFunctor t where
  mtIsoMap :: (m ~> n, n ~> m) -> t m ~> t n


-- }}}

-- MonadZero {{{

class (Monad m) => MonadZero m where
  mzero :: m a

guard :: (MonadZero m) => Bool -> m ()
guard True = return ()
guard False = mzero

-- }}}

-- MonadPlus {{{

class (Monad m) => MonadPlus m where
  (<+>) :: m a -> m a -> m a

msum :: (Iterable a t, MonadZero m, MonadPlus m) => t -> m a
msum = iter ((<+>) . return) mzero

msums :: (Iterable (m a) t, MonadZero m, MonadPlus m) => t -> m a
msums = iter (<+>) mzero

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

useMaybeZero :: (MonadZero m) => Maybe a -> m a
useMaybeZero Nothing = mzero
useMaybeZero (Just x) = return x

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

modify :: (MonadStateE s m) => (s -> s) -> m ()
modify f = stateE $ StateT $ \ s -> return ((), f s)

modifyP :: (MonadStateE s m) => P s -> (s -> s) -> m ()
modifyP P = modify

modifyL :: (MonadStateE s m) => Lens s a -> (a -> a) -> m ()
modifyL = modify .: update

-- Note about [localState :: (MonadStateE s m) => ...] {{{
-- Equivalent functionality can also be implemented with MonadStateE.
-- Although, for example, transforming (StateT s2 m a) with a (Lens s1 s2)
-- resulting in a (StateT s1 m a) only goes one direction, so only MonadStateE
-- can be converted in this form.
-- (Although, given the alternate implementation of localState with
-- MonadStateE, this doesn't prevent (MonadStateI s2 m, Lens s1 s2) =>
-- MonadStateI s1 m) }}}
localState :: (MonadStateI s m) => s -> m a -> m (a, s)
localState s aM = unStateT (stateI aM) s

next :: (MonadStateE s m, Peano s) => m s
next = do
  i <- get
  put $ psuc i
  return i

class (CMonad c m) => CMonadStateI c s m | m -> c where
  cstateI :: (m ~>~ StateT s m) c
class (CMonad c m) => CMonadStateE c s m | m -> c where
  cstateE :: (StateT s m ~>~ m) c
class (CMonadStateI c s m, CMonadStateE c s m) => CMonadState c s m | m -> c where

cget :: (CMonadStateE c s m, c s, c (s, s)) => m s
cget = cstateE $ StateT $ \ s -> creturn (s, s)

cgetP :: (CMonadStateE c s m, c s, c (s, s)) => P s -> m s
cgetP P = cget

cgetL :: (CMonadStateE c s m, c s, c (s, s), c a) => Lens s a -> m a
cgetL l = cmmap (access l) cget

cput :: (CMonadStateE c s m, c (), c ((), s)) => s -> m ()
cput s = cstateE $ StateT $ \ _ -> creturn ((), s)

cputP :: (CMonadStateE c s m, c (), c ((), s)) => P s -> s -> m ()
cputP P = cput

cputL :: (CMonadStateE c s m, c (), c ((), s)) => Lens s a -> a -> m ()
cputL = cmodify .: set

cmodify :: (CMonadStateE c s m, c (), c ((), s)) => (s -> s) -> m ()
cmodify f = cstateE $ StateT $ \ s -> creturn ((), f s)

cmodifyP :: (CMonadStateE c s m, c (), c ((), s)) => P s -> (s -> s) -> m ()
cmodifyP P = cmodify

cmodifyL :: (CMonadStateE c s m, c (), c ((), s)) => Lens s a -> (a -> a) -> m ()
cmodifyL = cmodify .: update

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
askL l = access l <$> ask

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

-- MonadRWST {{{

newtype RWST r o s m a = RWST { unRWST :: ReaderT r (WriterT o (StateT s m)) a }

class (MonadReaderI r m, MonadWriterI o m, MonadStateI s m) => MonadRWSI r o s m where
  rwsI :: m ~> RWST r o s m
class (MonadReaderE r m, MonadWriterE o m, MonadStateE s m) => MonadRWSE r o s m where
  rwsE :: RWST r o s m ~> m
class (MonadReader r m, MonadWriter o m, MonadState s m) => MonadRWS r o s m where

-- }}}

-- MonadListSetT {{{

newtype ListSetT m a = ListSetT { runListSetT :: m (ListSet a) }

class (Monad m) => MonadListSetI m where
  listSetI :: m ~> ListSetT m
class (Monad m) => MonadListSetE m where
  listSetE :: ListSetT m ~> m
class (MonadListSetI m, MonadListSetE m) => MonadListSet m where

-- }}}

----------
-- Data --
----------

-- Function {{{ --

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

rotateR :: (a -> b -> c -> d) -> (c -> a -> b -> d)
rotateR f c a b = f a b c

rotateL :: (a -> b -> c -> d) -> (b -> c -> a -> d)
rotateL f b c a = f a b c

mirror :: (a -> b -> c -> d) -> (c -> b -> a -> d)
mirror f c b a = f a b c

on :: (b -> b -> c) -> (a -> b) -> (a -> a -> c)
on p f x y = p (f x) (f y)

composeEndo :: [a -> a] -> a -> a
composeEndo = runEndo . concat . map Endo

-- }}} --

-- Tuple {{{

instance (PartialOrder a, PartialOrder b) => PartialOrder (a, b) where
  (a1, b1) <~ (a2, b2) = (a1 <~ a2) /\ (b1 <~ b2)
instance (HasBot a, HasBot b) => HasBot (a, b) where
  bot = (bot, bot)
instance (JoinLattice a, JoinLattice b) => JoinLattice (a, b) where
  (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)

fstL :: Lens (a, b) a
fstL = lens fst $ \ (_,b) -> (,b)

sndL :: Lens (a, b) b
sndL = lens snd $ \ (a,_) -> (a,)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

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
  toString = fromChars . Prelude.show

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  x _ = x
ifThenElse False _ y = y

cond :: (a -> Bool) -> c -> c -> (a -> c)
cond p t f x = if p x then t else f

-- }}} --

-- Sum {{{

data a :+: b = Inl a | Inr b

-- }}}

-- P {{{

data P a = P

-- }}}

-- Compose {{{

newtype (t :.: u) a = Compose { runCompose :: t (u a) }
newtype (t :..: u) m a = Compose2 { runCompose2 :: t (u m) a }

instance (Unit t, Unit u) => Unit (t :.: u) where
  unit = Compose . unit . unit

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
  toString = fromChars . Prelude.show

error :: String -> a
error = Prelude.error . toChars 

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
instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just x >>= k = k x
instance Applicative Maybe where (<@>) = mapply
instance Functor Maybe where map = mmap
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

maybe :: (a -> b) -> b -> Maybe a -> b
maybe _ i Nothing = i
maybe f _ (Just a) = f a

-- }}}

-- Set {{{

instance Iterable a (Set a) where
  iter = Set.foldl' . flip
instance CoIterable a (Set a) where
  coiter = Set.foldr
instance (Ord a) => Buildable a (Set a) where
  nil = sempty
  cons = sinsert
instance (Ord a) => SetLike a (Set a) where
  sempty = Set.empty
  ssingleton = Set.singleton
  sunion = Set.union
  (\-\) = (Set.\\)
  sintersection = Set.intersection
  (?) = flip Set.member
  ssize = fromInteger . toInteger . Set.size
instance CUnit Ord Set where
  cunit = ssingleton
instance CMonad Ord Set where
  (>>=~) = sunionMapOn
instance CFunctor Ord Set where
  cmap = Set.map
instance (Ord a) => PartialOrder (Set a) where
  (<~) = Set.isSubsetOf
instance HasBot (Set a) where
  bot = Set.empty
instance (Ord a) => JoinLattice (Set a) where
  (\/) = sunion

smember :: (SetLike a t) => a -> t -> Bool
smember = flip (?)

sinsert :: (SetLike a t) => a -> t -> t
sinsert = sunion . ssingleton

smap :: (Iterable a t, SetLike b u) => (a -> b) -> t -> u
smap f = iter (sinsert . f) sempty

useMaybeSet :: (SetLike a t) => Maybe a -> t
useMaybeSet Nothing = sempty
useMaybeSet (Just a) = ssingleton a

sset :: (Iterable a t, SetLike a u) => t -> u
sset = iter sinsert sempty

sisEmpty :: (SetLike a t) => t -> Bool
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
instance Integral Int where
instance ToString Int where
  toString = fromChars . Prelude.show

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
  toString = fromChars . Prelude.show

-- }}}

-- IO {{{

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

udpateM :: (Monad m) => Lens a b -> (b -> m b) -> a -> m a
udpateM l f a =
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
instance Unit [] where
  unit = (:[])
instance MonadPlus [] where
  (<+>) = (++)
instance Monad [] where
  []     >>= _ = []
  (x:xs) >>= k = k x ++ (xs >>= k)
instance Applicative [] where
  []     <*> _  = []
  (x:xs) <*> ys = map (x,) ys ++ xs <*> ys
instance MonadZero [] where
  mzero = []
instance MonadMaybeE [] where
  maybeE :: MaybeT [] ~> []
  maybeE aM = do
    aM' <- runMaybeT aM
    case aM' of
      Nothing -> mzero
      Just x -> return x

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

pluck :: [[a]] -> ([a], [[a]])
pluck [] = ([], [])
pluck ([]:xss) = pluck xss
pluck ((x:xs):xss) = let
  (xs', xss') = pluck xss
  in (x:xs', xs:xss')

transpose :: [[a]] -> [[a]]
transpose [] = []
transpose ([]:xss) = transpose xss
transpose xss =
  let (xs, xss') = pluck xss
  in xs : transpose xss'

-- }}}

-- ListSet {{{

newtype ListSet a = ListSet { runListSet :: [a] }
  deriving (Monoid, Unit, Functor, Applicative, Monad, MonadPlus, Iterable a, CoIterable a)
instance HasBot (ListSet a) where
  bot = ListSet []
instance JoinLattice (ListSet a) where
  xs1 \/ xs2 = ListSet $ runListSet xs1 ++ runListSet xs2

-- }}}

-- Endo {{{

data Endo a = Endo { runEndo :: a -> a }
instance Monoid (Endo a) where
  null = Endo id
  g ++ f = Endo $ runEndo g . runEndo f

-- }}}

-- Annotated {{{

data Annotated ann a = Annotated
  { annotation :: ann
  , annValue :: a
  }

-- }}}

-- Fix {{{

newtype Fix f = Fix { runFix :: f (Fix f) }

-- }}}
