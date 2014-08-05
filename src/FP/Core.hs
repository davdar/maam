module FP.Core 

-- Exports {{{

  ( module Prelude
  , module FP.Core
  , module GHC.Exts
  , module Data.Set
  , module Data.Map
  ) where

-- }}}

-- Imports {{{

import qualified Prelude
import Prelude 
  ( Eq(..), Ord(..)
  , (.), ($), const, flip, curry, uncurry
  , Bool(..), (||), (&&), not, otherwise
  , Char, Int, Integer, Double, Rational
  , Maybe(..)
  , error, undefined, seq
  , IO
  )
import Data.ByteString.Char8 (ByteString)
import GHC.Exts (type Constraint)
import qualified Data.ByteString.Char8 as BS
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)


infixl 9 #
infixl 9 #!
infixl 9 <@>
infixr 9 <.>

infix 7 /
infix 7 //
infixr 7 *
infixr 7 <*>
infixr 7 /\

infix 6 -
infixr 6 +
infixr 6 <+>
infixr 6 \/

infix 4 <~
infix 4 <.
infix 4 ?

infixl 1 >>=
infixl 1 >>
infixl 1 >>~

infixr 0 *$
infixr 0 *$~
infixr 0 <$>
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

class JoinLattice a where
  bot :: a
  (\/) :: a -> a -> a

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

class CoIterable a t | t -> a where
  coiter :: (a -> b -> b) -> b -> t -> b

-- }}}

-- Functorial {{{

class Functorial c t where
  functorial :: (c a) => W (c (t a))

class Bifunctorial c t where
  bifunctorial :: (c a, c b) => W (c (t a b))

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

-- }}}

-- SetLike {{{

class (Iterable e t) => SetLike e t | t -> e where
  sempty :: t
  ssingleton :: e -> t
  sunion :: t -> t -> t
  sintersection :: t -> t -> t
  (?) :: t -> e -> Bool
  ssize :: (Integral n) => t -> n

unionMap :: (Iterable a t, SetLike b u) => (a -> u) -> t -> u
unionMap f = iter (sunion . f) sempty

eachUnion :: (Iterable a t, SetLike b u) => t -> (a -> u) -> u
eachUnion = flip unionMap

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

eachM :: (FunctorM t, Monad m) => t a -> (a -> m b) -> m (t b)
eachM = flip mapM

-- }}}

-- Applicative {{{

class (Unit t, Functor t) => Applicative t where
  (<*>) :: t a -> t b -> t (a, b)
  aT <*> bT = unit (,) <@> aT <@> bT
  (<@>) :: t (a -> b) -> t a -> t b
  fT <@> aT = map (uncurry ($)) $ fT <*> aT

-- }}}

-- Monad {{{

class Unit t where
  unit :: a -> t a

class (Functor m, Applicative m) => Monad m where
  (>>=) :: m a -> (a -> m b) -> m b

return :: (Monad m) => a -> m a
return = unit

(>>) :: (Monad m) => m a -> m b -> m b
aM >> bM = aM >>= const bM

extend :: (Monad m) => (a -> m b) -> (m a -> m b)
extend = flip (>>=)

(*$) :: (Monad m) => (a -> m b) -> (m a -> m b)
(*$) = extend

mmap :: (Monad m) => (a -> b) -> m a -> m b
mmap f aM = do
  a <- aM
  return $ f a

mapply :: (Monad m) => m (a -> b) -> m a -> m b
mapply fM aM = do
  f <- fM
  a <- aM
  return $ f a

class CMonad c m | m -> c where
  creturn :: (c a) => a -> m a
  (>>~) :: (c a, c b) => m a -> (a -> m b) -> m b

(*$~) :: (CMonad c m, c a, c b) => (a -> m b) -> (m a -> m b)
(*$~) = flip (>>~)

class (Monad m) => MonadFail m where
  fail :: Chars -> m a

class (Monad m) => MonadZero m where
  mzero :: m a

class (Monad m) => MonadPlus m where
  (<+>) :: m a -> m a -> m a

msum :: (Iterable a t, MonadZero m, MonadPlus m) => t -> m a
msum = iter ((<+>) . return) mzero

type m ~> n = forall a. m a -> n a

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
getL l = mmap (access l) get

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
instance (JoinLattice b) => JoinLattice (a -> b) where
  bot = const bot
  (\/) f g x = f x \/ g x
instance (MeetLattice b) => MeetLattice (a -> b) where
  top = const top
  (/\) f g x = f x /\ g x
instance (Lattice b) => Lattice (a -> b) where

applyTo :: a -> (a -> b) -> b
applyTo = flip ($)

(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)

rotateR :: (a -> b -> c -> d) -> (c -> a -> b -> d)
rotateR f c a b = f a b c

rotateL :: (a -> b -> c -> d) -> (b -> c -> a -> d)
rotateL f b c a = f a b c

mirror :: (a -> b -> c -> d) -> (c -> b -> a -> d)
mirror f c b a = f a b c

-- }}} --

-- Bool {{{ --

instance JoinLattice Bool where
  bot = False
  (\/) = (||)
instance MeetLattice Bool where
  top = True
  (/\) = (&&)
instance Dual Bool where
  dual = not

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  x _ = x
ifThenElse False _ y = y

-- }}} --

-- Sum {{{

data a :+: b = Inl a | Inr b

-- }}}

-- P {{{

data P a = P

-- }}}

-- Point {{{

data Pointed a = Top | Bot | Point a

instance (Eq a) => JoinLattice (Pointed a) where
  bot = Bot
  Top     \/ _   = Top
  _       \/ Top = Top
  Bot     \/ p   = p
  p       \/ Bot = p
  Point x \/ Point y 
    | x == y = Point x
    | otherwise = Top

-- }}}

-- String {{{

type String = ByteString
type Chars = [Char]

instance ToChars String where
  toChars = BS.unpack
instance FromChars String where
  fromChars = BS.pack

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

unsafeCoerceJust :: Maybe a -> a
unsafeCoerceJust (Just a) = a
unsafeCoerceJust Nothing = error $ toChars "expected Just but found Nothing"

-- }}}

-- ID {{{

newtype ID a = ID { runID :: a }

instance Unit ID where
  unit = ID
instance Monad ID where
  ID x >>= k = k x
instance Applicative ID where (<@>) = mapply 
instance Functor ID where map = mmap
 

-- }}}

-- Set {{{

instance Iterable a (Set a) where
  iter = Set.foldl' . flip
instance (Ord a) => SetLike a (Set a) where
  sempty = Set.empty
  ssingleton = Set.singleton
  sunion = Set.union
  sintersection = Set.intersection
  (?) = flip Set.member
  ssize = fromInteger . toInteger . Set.size
instance CMonad Ord Set where
  creturn = ssingleton
  (>>~) = eachUnion
instance (Ord a) => JoinLattice (Set a) where
  bot = sempty
  (\/) = sunion

smember :: (SetLike a t) => a -> t -> Bool
smember = flip (?)

-- }}}

-- Map {{{

instance Iterable (k, v) (Map k v) where
  iter f = Map.foldlWithKey $ \ b k v -> f (k, v) b
instance (Ord k) => Indexed k v (Map k v) where
  p # k = Map.lookup k p
  
instance (Ord k) => MapLike k v (Map k v) where
  pempty = Map.empty
  psingleton = Map.singleton
  punionWith = Map.unionWith
  pintersectionWith = Map.intersectionWith
  pmodify = Map.adjust
  psize = fromInteger . toInteger . Map.size

-- }}}

-- Int {{{

instance FromInteger Int where
  fromInteger = Prelude.fromIntegral
instance ToInteger Int where
  toInteger = Prelude.toInteger

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
  in mmap ba $ f b

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

zip :: [a] -> [b] -> [(a, b)]
zip [] _ = []
zip _ [] = []
zip (x:xs) (y:ys) = (x,y):zip xs ys

zipSameLength :: [a] -> [b] -> Maybe [(a, b)]
zipSameLength [] [] = Just []
zipSameLength [] (_:_) = Nothing
zipSameLength (_:_) [] = Nothing
zipSameLength (x:xs) (y:ys) = do
  xys <- zipSameLength xs ys
  return $ (x, y):xys

-- }}}
