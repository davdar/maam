module FP.Core 

-- Exports {{{

  ( module Prelude
  , module FP.Core
  , module GHC.Exts
  , module Data.Char
  ) where

-- }}}

-- Imports {{{

import qualified Prelude
import Prelude 
  ( Eq(..), Ord(..), Ordering(..)
  , id, (.), ($), const, flip, curry, uncurry
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
import Data.Char (isSpace, isAlphaNum, isLetter, isDigit)

-- }}}

-- Precedence {{{

infix 9 ?
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

infixl 1 >>=
infixl 1 >>
infixr 1 ~>

infixr 0 *$
infixr 0 ^$
infixr 0 ^*$
infixr 0 <$>
-- infixr 0 ^*$~

infixr 0 ~:
infixr 0 =:
infixr 0 |:

-- }}}

-------------
-- Classes --
-------------

-- Constraint {{{ 

data W (c :: Constraint) where
  W :: (c) => W c

with :: W c -> (c => a) -> a
with W x = x

class Universal a where
instance Universal a

class (c1 a, c2 a) => (c1 ::*:: c2) a where
instance (c1 a, c2 a) => (c1 ::*:: c2) a where

class (t (u a)) => (t ::.:: u) a where
instance (t (u a)) => (t ::.:: u) a where

class (c1 ::=>:: c2) where
  impl :: (c1) => W c2

class Functorial c t where
  functorial :: (c a) => W (c (t a))

class Bifunctorial c t where
  bifunctorial :: (c a, c b) => W (c (t a b))

bifunctorialP :: (Bifunctorial c t, c a, c b) => P c -> P t -> P a -> P b -> W (c (t a b))
bifunctorialP P P P P = bifunctorial

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

class ToChars a where
  toChars :: a -> Chars
class FromChars a where
  fromChars :: Chars -> a

-- for Overlaoded Strings extension
fromString :: Chars -> String
fromString = fromChars

class ToString t where
  toString :: t -> String
class FromString t where
  fromString' :: String -> t

-- }}}

-- Commute {{{

class Commute t u where
  commute :: t (u a) -> u (t a)

-- }}}

-- Arithmetic {{{ --

class Peano a where
  zer :: a
  suc :: a -> a

niter :: (Eq a, Peano a) => (b -> b) -> b -> a -> b
niter f i0 x = loop i0 zer
  where
    loop i j
      | j == x = i
      | otherwise = 
        let i' = f i
        in i' `seq` loop i' $ suc j

niterOn :: (Eq a, Peano a) => a -> b -> (b -> b) -> b
niterOn = mirror niter

class (Peano a) => Additive a where
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

class 
  ( TruncateDivisible a
  , ToInteger a, FromInteger a
  , ToInt a, FromInt a
  , ToRational a
  , ToDouble a
  ) => Integral a where
class 
  ( Divisible a
  , ToRational a, FromRational a
  , ToDouble a, FromDouble a
  , FromInteger a
  , FromInt a
  ) => Floating a where

-- }}}

-- Category {{{ --

class Category t where
  catid :: t a a
  (<.>) :: t b c -> t a b -> t a c

-- }}} --

-- Morphism {{{

type m ~> n = forall a. m a -> n a
type t ~~> u = forall a m. t m a -> u m a

class Morphism a b where
  morph :: a -> b
class Morphism2 m n where
  morph2 :: m ~> n
class Morphism3 t u where
  morph3 :: t ~~> u

-- }}}

-- Isomorphism {{{

class (Morphism a b, Morphism b a) => Isomorphism a b where

isoto :: (Isomorphism a b) => a -> b
isoto = morph

isofrom :: (Isomorphism a b) => b -> a
isofrom = morph

class (Morphism2 t u, Morphism2 u t) => Isomorphism2 t u where

isoto2 :: (Isomorphism2 t u) => t ~> u
isoto2 = morph2

isofrom2 :: (Isomorphism2 t u) => u ~> t
isofrom2 = morph2

onIso2 :: (Isomorphism2 t u) => (u a -> u b) -> t a -> t b
onIso2 f = isofrom2 . f . isoto2

class (Morphism3 v w, Morphism3 w v) => Isomorphism3 v w where

isoto3 :: (Isomorphism3 v w) => v ~~> w
isoto3 = morph3

isofrom3 :: (Isomorphism3 v w) => w ~~> v
isofrom3 = morph3

-- }}}

-- PartialOrder {{{

data POrdering = PEQ | PLT | PGT | PUN

fromOrdering :: Ordering -> POrdering
fromOrdering EQ = PEQ
fromOrdering LT = PLT
fromOrdering GT = PGT

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

-- Monoid {{{

class Monoid a where
  null :: a
  (++) :: a -> a -> a

iterateAppend :: (Monoid a, Eq n, Peano n) => n -> a -> a
iterateAppend n a = niterOn n null (a ++)

-- }}}

-- Lattice {{{ --

class JoinLattice a where
  bot :: a
  (\/) :: a -> a -> a

collect :: (JoinLattice a, PartialOrder a) => (a -> a) -> a -> a
collect f = poiter $ \ x -> x \/ f x

collectN :: (JoinLattice a, PartialOrder a, Eq n, Peano n) => n -> (a -> a) -> a -> a
collectN n f x0 = niterOn n x0 $ \ x -> x \/ f x

class MeetLattice a where
  top :: a
  (/\) :: a -> a -> a

class (JoinLattice a, MeetLattice a) => Lattice a where

-- }}} --

-- Unit {{{

class Unit t where
  unit :: a -> t a

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

-- }}}

-- Applicative {{{

class Product t where
  (<*>) :: t a -> t b -> t (a, b)

class Applicative t where
  (<@>) :: t (a -> b) -> t a -> t b

(<$>) :: (Applicative t) => t (a -> b) -> t a -> t b
(<$>) = (<@>)

-- }}}

-- Monad {{{

class Bind (m :: * -> *) where
  (>>=) :: m a -> (a -> m b) -> m b
class (Unit m, Functor m, Product m, Applicative m, Bind m) => Monad m where

fail :: Chars -> m a
fail = Prelude.error

return :: (Monad m) => a -> m a
return = unit

kleisli :: (Monad m) => (a -> b) -> (a -> m b)
kleisli = (.) return

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

-- }}}

-- Monad Transformers {{{

class Unit2 t where
  unit2 :: m ~> t m
class Join2 t where
  join2 :: t (t m) ~> t m
class Functor2 t where
  map2 :: (m ~> n) -> t m ~> t n
class IsoFunctor2 t where
  isoMap2 :: (m ~> n) -> (n ~> m) -> t m ~> t n

class FunctorUnit2 t where
  funit2 :: (Functor m) => m ~> t m
class FunctorJoin2 t where
  fjoin2 :: (Functor m) => t (t m) ~> t m
class FunctorFunctor2 t where
  fmap2 :: (Functor m, Functor n) => (m ~> n) -> t m ~> t n
class FunctorIsoFunctor2 t where
  fisoMap2 :: (Functor m, Functor n) => (m ~> n) -> (n ~> m) -> t m ~> t n

class MonadUnit2 t where
  munit2 :: (Monad m) => m ~> t m
class MonadJoin2 t where
  mjoin2 :: (Monad m) => t (t m) ~> t m
class MonadFunctor2 t where
  mmap2 :: (Monad m, Monad n) => (m ~> n) -> t m ~> t n
class MonadIsoFunctor2 t where
  misoMap2 :: (Monad m, Monad n) => (m ~> n) -> (n ~> m) -> t m ~> t n

-- }}}

-- MonadZero {{{

class MonadZero (m :: * -> *) where
  mzero :: m a

guard :: (Unit m, MonadZero m) => Bool -> m ()
guard True = unit ()
guard False = mzero

maybe :: (Unit m, MonadZero m) => Maybe a -> m a
maybe Nothing = mzero
maybe (Just a) = unit a

-- }}}

-- MonadConcat {{{

class MonadConcat (m :: * -> *) where
  (<++>) :: m a -> m a -> m a

-- }}}

-- MonadPlus {{{

class MonadPlus (m :: * -> *) where
  (<+>) :: m a -> m a -> m a

oneOrMore :: (Monad m, MonadZero m, MonadConcat m) => m a -> m (a, [a])
oneOrMore aM = do
  x <- aM
  xs <- many aM
  return (x, xs)

twoOrMore :: (Monad m, MonadZero m, MonadConcat m) => m a -> m (a, a, [a])
twoOrMore aM = do
  x1 <- aM
  (x2, xs) <- oneOrMore aM
  return (x1, x2, xs)

oneOrMoreList :: (Monad m, MonadZero m, MonadConcat m) => m a -> m [a]
oneOrMoreList = uncurry (:) ^. oneOrMore

many :: (Monad m, MonadZero m, MonadConcat m) => m a -> m [a]
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

maybeM :: (MonadMaybeE m) => m (Maybe a) -> m a
maybeM = maybeE . MaybeT

lookMaybe :: (MonadMaybeI m) => m a -> m (Maybe a)
lookMaybe = runMaybeT . maybeI

abort :: (MonadMaybeE m) => m a
abort = maybeM $ return Nothing

(<|>) :: (MonadMaybeI m) => m a -> m a -> m a
aM1 <|> aM2 = do
  aM' <- lookMaybe aM1
  case aM' of
    Just a -> return a
    Nothing -> aM2

maybeZero :: (Unit m, MonadZero m) => Maybe a -> m a
maybeZero Nothing = mzero
maybeZero (Just x) = unit x

-- }}}

-- MonadError {{{

newtype ErrorT e m a = ErrorT { runErrorT :: m (e :+: a) }

class (Monad m) => MonadErrorI e m where
  errorI :: m ~> ErrorT e m
class (Monad m) => MonadErrorE e m where
  errorE :: ErrorT e m ~> m
class (MonadErrorI e m, MonadErrorE e m) => MonadError e m where

useSum :: (MonadErrorE e m) => e :+: a -> m a
useSum = errorE . ErrorT . return

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
modify = modifyM . kleisli

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
  put $ suc i
  return i

nextL :: (MonadStateE s m, Peano a) => Lens s a -> m a
nextL l = do
  i <- getL l
  putL l $ suc i
  return i

bumpL :: (MonadStateE s m, Peano a) => Lens s a -> m ()
bumpL l = modifyL l suc

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

class (Bind m) => MonadSetI m where
  setI :: m ~> SetT m
class (Bind m) => MonadSetE m where
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

-- Iterable {{{

class Iterable a t | t -> a where
  -- the left fold, exposing the fold continuation
  foldlk :: forall b. (a -> b -> (b -> b) -> b) -> b -> t -> b
  foldlk f i t = foldl (\ a (bK :: (b -> b) -> b) (k :: b -> b) -> bK $ \ b -> f a b k) ($ i) t id
  -- the left fold
  foldl :: (a -> b -> b) -> b -> t -> b
  foldl f = foldlk $ \ a b k -> k $ f a b
  -- the right fold
  foldr :: (a -> b -> b) -> b -> t -> b
  foldr f = foldlk $ \ a b k -> f a $ k b
  -- the most efficient fold (unspecified order)
  iter :: (a -> b -> b) -> b -> t -> b
  iter = foldl
  size :: (Integral n) => t -> n
  size = iter (const suc) 0

concat :: (Iterable a t, Monoid a) => t -> a
concat = foldr (++) null

mconcat :: (Iterable (m a) t, MonadZero m, MonadConcat m) => t -> m a
mconcat = foldr (<++>) mzero

mtry :: (MonadMaybe m) => [m a] -> m a
mtry = foldr (<|>) abort

joins :: (Iterable a t, JoinLattice a) => t -> a
joins = iter (\/) bot

msum :: (Iterable (m a) t, MonadZero m, MonadPlus m) => t -> m a
msum = iter (<+>) mzero

munion :: (Iterable a t, MonadZero m, Unit m, MonadPlus m) => t -> m a
munion = iter ((<+>) . unit) mzero

iterOn :: (Iterable a t) => t -> b -> (a -> b -> b) -> b
iterOn = mirror iter

iterFrom :: (Iterable a t) => b -> (a -> b -> b) -> t -> b
iterFrom = flip iter

findMax :: (Iterable a t, PartialOrder b) => (a -> b) -> a -> t -> a
findMax p i0 = iterFrom i0 $ \ a i -> if p a <~ p i then a else i

findMaxFrom :: (Iterable a t, PartialOrder b) => a -> (a -> b) -> t -> a
findMaxFrom = flip findMax

isElem :: (Iterable a t, Eq a) => a -> t -> Bool
isElem x = foldlk (\ x' _ k -> if x == x' then True else k False) False

elemAtN :: (Iterable a t, Peano n, Eq n) => n -> t -> Maybe a
elemAtN n t = case foldlk ff (Inr zer) t of
  Inl x -> Just x
  Inr _ -> Nothing
  where
    ff x' (Inr i) k = if i == n then Inl x' else k $ Inr $ suc i
    ff _ (Inl _) _ = error "internal error"

traverse :: (Iterable a t, Monad m) => (a -> m ()) -> t -> m ()
traverse f = foldr (\ a m -> m >> f a) $ return ()

traverseOn :: (Iterable a t, Monad m) => t -> (a -> m ()) -> m ()
traverseOn = flip traverse

exec :: (Iterable (m ()) t, Monad m) => t -> m ()
exec = traverse id

toList :: (Iterable a t) => t -> [a]
toList = foldr (:) []

-- }}}

-- Container {{{

class Container e t | t -> e where
  (?) :: t -> e -> Bool

elem :: (Container e t) => e -> t -> Bool
elem = flip (?)

-- }}}

-- Indexed {{{

class Indexed k v t | t -> k, t -> v where
  (#) :: t -> k -> Maybe v

(#!) :: (Indexed k v t) => t -> k -> v
(#!) = unsafe_coerce justL .: (#)

lookup :: (Indexed k v t) => k -> t -> Maybe v
lookup = flip (#)

-- }}}

-- ListLike {{{

-- Minimal definitino: nil cons uncons
class (Iterable a t) => ListLike a t | t -> a where
  nil :: t
  isNil :: t -> Bool
  isNil = isL nothingL . uncons
  cons :: a -> t -> t
  uncons :: t -> Maybe (a, t)

toListLike :: (ListLike a t) => [a] -> t
toListLike = foldr cons nil

fromListLike :: (ListLike a t) => t -> [a]
fromListLike = foldr cons nil

single :: a -> [a]
single = flip (:) []

filter :: (a -> Bool) -> [a] -> [a]
filter p = foldr (\ x -> if p x then (x :) else id) []

zip :: [a] -> [b] -> Maybe [(a, b)]
zip [] [] = return []
zip (_:_) [] = Nothing
zip [] (_:_) = Nothing
zip (x:xs) (y:ys) = do
  xys <- zip xs ys
  return $ (x,y) : xys

unzip :: [(a, b)] -> ([a], [b])
unzip [] = ([], [])
unzip ((x, y):xys) =
  let (xs, ys) = unzip xys
  in (x:xs, y:ys)

replicate :: (Eq n, Peano n) => n -> a -> [a]
replicate n = niterOn n [] . (:)

firstN :: (Eq n, Integral n) => n -> [a] -> [a]
firstN n = recur 0
  where
    recur _ [] = []
    recur i (x:xs)
      | i == n = []
      | otherwise = x : recur (suc i) xs

intersperse :: a -> [a] -> [a]
intersperse _ [] = []
intersperse _ [x] = [x]
intersperse i (x:xs) = x : recur xs
  where
    recur [] = []
    recur (x':xs') = i : x' : recur xs'

mapRest :: (a -> a) -> [a] -> [a]
mapRest _ [] = []
mapRest f (x:xs) = x:map f xs

head :: [a] -> Maybe a
head [] = Nothing
head (x:_) = Just x

tail :: [a] -> Maybe [a]
tail [] = Nothing
tail (_:xs) = Just xs

-- }}}

-- SetLike {{{

-- Minimal definition: empty, insert, remove
class (Iterable e t, Container e t) => SetLike e t | t -> e where
  learnSet :: t -> b -> ((Ord e) => b) -> b
  empty :: t
  isEmpty :: t -> Bool
  isEmpty = isL nothingL . remove
  insert :: (Ord e) => e -> t -> t
  remove :: t -> Maybe (e, t)
  union :: t -> t -> t
  union s1 s2 = learnSet s2 s1 $ iter insert s2 s1
  intersection :: t -> t -> t
  intersection s1 s2 = s1 \-\ (s1 \-\ s2)
  (\-\) :: t -> t -> t
  s1 \-\ s2 = learnSet s2 s1 $ iter (\ e -> if s2 ? e then id else insert e) empty s1

singleton :: (Ord e) => e -> Set e
singleton = flip insert empty

setMap :: (Ord b) => (a -> b) -> Set a -> Set b
setMap f = iter (insert . f) empty

maybeSet :: (Ord a) => Maybe a -> Set a
maybeSet Nothing = empty
maybeSet (Just a) = singleton a

toSet :: (SetLike a t, Ord a) => [a] -> t
toSet = iter insert empty

fromSet :: (SetLike a t) => t -> [a]
fromSet = iter (:) []

-- }}}

-- MapLike {{{

-- Minimal definition: mapEmpty, mapIsEmpty, mapInsertWith, mapRemove
class (Iterable (k,v) t, Indexed k v t) => MapLike k v t | t -> k, t -> v where
  learnMap :: t -> b -> ((Ord k) => b) -> b
  mapEmpty :: t
  mapIsEmpty :: t -> Bool
  mapInsertWith :: (Ord k) => (v -> v -> v) -> k -> v -> t -> t
  mapRemove :: t -> Maybe ((k, v), t)
  mapUnionWith :: (v -> v -> v) -> t -> t -> t
  mapUnionWith f m1 m2 = learnMap m2 m1 $ iter (\ (k,v) -> mapInsertWith f k v) m2 m1
  mapIntersectionWith :: (v -> v -> v) -> t -> t -> t
  mapIntersectionWith f m1 m2 = 
    learnMap m2 mapEmpty $
    iterOn (mapKeys m1 `union` mapKeys m2) mapEmpty $ \ k ->
      case (m1 # k, m2 # k) of
        (Nothing, Nothing) -> id
        (Just v, Nothing) -> mapInsert k v
        (Nothing, Just v) -> mapInsert k v
        (Just v1, Just v2) -> mapInsert k $ f v1 v2
  mapModify :: (v -> v) -> k -> t -> t
  mapModify f k m = 
    learnMap m mapEmpty $
    case m # k of
      Nothing -> m
      Just v -> mapInsert k (f v) m
  mapKeys :: t -> Set k
  mapKeys m = learnMap m empty $ iter (insert . fst) empty m

mapInsert :: (MapLike k v t, Ord k) => k -> v -> t -> t
mapInsert = mapInsertWith $ const id

onlyKeys :: (SetLike k t, MapLike k v u) => t -> u -> u
onlyKeys t u = learnMap u mapEmpty $ iter (\ k -> maybeElim id (mapInsert k) $ u # k) mapEmpty t

toMap :: (MapLike k v t, Ord k) => [(k,v)] -> t
toMap = iter (uncurry mapInsert) mapEmpty

fromMap :: (MapLike k v t) => t -> [(k,v)]
fromMap = iter (:) []

-- }}}

----------
-- Data --
----------

-- P {{{

data P a = P

-- }}}

-- Lens {{{

data Cursor a b = Cursor { focus :: a, construct :: a -> b }
data Lens a b = Lens { runLens :: a -> Cursor b a }

lens :: (a -> b) -> (a -> b -> a) -> Lens a b
lens getter setter = Lens $ \ s -> Cursor (getter s) (setter s)

isoLens :: (a -> b) -> (b -> a) -> Lens a b
isoLens to from = lens to $ const from

instance Category Lens where
  catid = isoLens id id
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

-- }}}

-- Prism {{{

data Prism a b = Prism { coerce :: a -> Maybe b, inject :: b -> a }

unsafe_coerce :: Prism a b -> a -> b
unsafe_coerce p a = case coerce p a of
  Nothing -> error "unsafe_coerce"
  Just b -> b

prism :: (a -> Maybe b) -> (b -> a) -> Prism a b
prism = Prism

isoPrism :: (a -> b) -> (b -> a) -> Prism a b
isoPrism to from = prism (Just . to) from

instance Category Prism where
  catid = isoPrism id id
  g <.> f = Prism
    { coerce = coerce g *. coerce f
    , inject = inject f . inject g
    }

isL :: Prism a b -> a -> Bool
isL p a = case coerce p a of
  Just _ -> True
  Nothing -> False

alter :: Prism a b -> (b -> b) -> a -> a
alter p f a = maybeElim a (inject p . f) $ coerce p a

pset :: Prism a b -> b -> a -> a
pset p = alter p . const

(~^) :: Prism a b -> (b -> b) -> a -> a
(~^) = alter

-- }}}

-- Function {{{

instance Category (->) where
  catid = id
  (<.>) = (.)
instance Functor ((->) a) where
  map = (.)
instance (Monoid b) => Monoid (a -> b) where
  null = const null
  (++) f g x = f x ++ g x
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

composition :: [a -> a] -> a -> a
composition = unEndo . concat . map Endo

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

-- Bool {{{ --

instance JoinLattice Bool where
  bot = False
  (\/) = (||)
instance MeetLattice Bool where
  top = True
  (/\) = (&&)
instance Monoid Bool where
  null = bot
  (++) = (\/)
instance ToString Bool where
  toString = preludeShow

fif :: Bool -> a -> a -> a
fif True x _ = x
fif False _ y = y

cond :: (a -> Bool) -> c -> c -> (a -> c)
cond p t f x = if p x then t else f

ifThenElse :: Bool -> a -> a -> a
ifThenElse = fif

-- }}} --

-- Char {{{

instance ToString Char where
  toString = preludeShow

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
instance Iterable Char String where
  foldl = Text.foldl' . flip
  foldr = Text.foldr
  iter = foldl
  size = fromInt . Text.length
instance ToString String where
  toString = preludeShow

error :: String -> a
error = Prelude.error . toChars 

preludeShow :: (Prelude.Show a) => a -> String
preludeShow = fromChars . Prelude.show

-- }}}

-- Int {{{

instance FromInteger Int where
  fromInteger = Prelude.fromIntegral
instance ToInteger Int where
  toInteger = Prelude.toInteger
instance Peano Int where
  zer = 0
  suc = Prelude.succ
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
instance ToRational Int where
  toRational = Prelude.fromIntegral
instance ToDouble Int where
  toDouble = Prelude.fromIntegral
instance Integral Int where
instance ToString Int where
  toString = preludeShow
instance PartialOrder Int where
  pcompare = fromOrdering .: compare
instance JoinLattice Int where
  bot = Prelude.minBound
  x \/ y = Prelude.max x y

-- }}}

-- Integer {{{

instance FromInteger Integer where
  fromInteger = id
instance ToInteger Integer where
  toInteger = id
instance Peano Integer where
  zer = 0
  suc = Prelude.succ
instance Additive Integer where
  zero = 0
  (+) = (Prelude.+)
instance Subtractive Integer where
  (-) = (Prelude.-)
instance Multiplicative Integer where
  one = 1
  (*) = (Prelude.*)
instance TruncateDivisible Integer where
  (//) = Prelude.div
instance ToString Integer where
  toString = preludeShow
instance ToInt Integer where
  toInt = Prelude.fromIntegral
instance FromInt Integer where
  fromInt = Prelude.fromIntegral
instance ToRational Integer where
  toRational = Prelude.fromIntegral
instance ToDouble Integer where
  toDouble = Prelude.fromIntegral
instance Integral Integer where

-- }}}

-- Tuple {{{

instance (PartialOrder a, PartialOrder b) => PartialOrder (a, b) where
  (a1, b1) <~ (a2, b2) = (a1 <~ a2) /\ (b1 <~ b2)
instance (Monoid a, Monoid b) => Monoid (a, b) where
  null = (null, null)
  (a1, b1) ++ (a2, b2) = (a1 ++ a2, b1 ++ b2)
instance (JoinLattice a, JoinLattice b) => JoinLattice (a, b) where
  bot = (bot, bot)
  (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)
instance Bifunctorial Eq (,) where
  bifunctorial = W
instance Bifunctorial Ord (,) where
  bifunctorial = W

swap :: (a, b) -> (b, a)
swap (x, y) = (y, x)

fstL :: Lens (a, b) a
fstL = lens fst $ \ (_,b) -> (,b)

sndL :: Lens (a, b) b
sndL = lens snd $ \ (a,_) -> (a,)

mapFst :: (a -> a') -> (a, b) -> (a', b)
mapFst f (a, b) = (f a, b)

mapSnd :: (b -> b') -> (a, b) -> (a, b')
mapSnd f (a, b) = (a, f b)

-- }}}

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

instance MonadErrorE a ((:+:) a) where
  errorE :: ErrorT a ((:+:) a) b -> a :+: b
  errorE aME = case runErrorT aME of
    Inl a -> Inl a
    Inr (Inl a) -> Inl a
    Inr (Inr b) -> Inr b
instance MonadErrorI a ((:+:) a) where
  errorI :: a :+: b -> ErrorT a ((:+:) a) b
  errorI ab = ErrorT $ Inr ab

inlL :: Prism (a :+: b) a
inlL = Prism
  { coerce = \ ab -> case ab of
      Inl a -> Just a
      Inr _ -> Nothing
  , inject = Inl
  }

inrL :: Prism (a :+: b) b
inrL = Prism
  { coerce = \ ab -> case ab of
      Inl _ -> Nothing
      Inr b -> Just b
  , inject = Inr
  }

mapInl :: (a -> a') -> a :+: b -> a' :+: b
mapInl f (Inl a) = Inl $ f a
mapInl _ (Inr a) = Inr a

mapInr :: (b -> b') -> a :+: b -> a :+: b'
mapInr _ (Inl a) = Inl a
mapInr f (Inr b) = Inr $ f b

-- }}}

-- Compose {{{

newtype (t :.: u) a = Compose { runCompose :: t (u a) }
  deriving (Eq, Ord, JoinLattice, PartialOrder)

onComposeIso :: (t (u a) -> t (u b)) -> (t :.: u) a -> (t :.: u) b
onComposeIso f (Compose x) = Compose $ f x
instance (Unit t, Unit u) => Unit (t :.: u) where
  unit = Compose . unit . unit
instance (Functor t, Functor u) => Functor (t :.: u) where
  map = onComposeIso . map . map

newtype (t :..: u) m a = Compose2 { runCompose2 :: t (u m) a }

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

nothingL :: Prism (Maybe a) ()
nothingL = Prism
  { coerce = \ aM -> case aM of
      Nothing -> Just ()
      Just _ -> Nothing
  , inject = \ () -> Nothing
  }

justL :: Prism (Maybe a) a
justL = Prism
  { coerce = id
  , inject = Just
  }

maybeElim :: b -> (a -> b) -> Maybe a -> b
maybeElim i _ Nothing = i
maybeElim _ f (Just a) = f a

maybeElimOn :: Maybe a -> b -> (a -> b) -> b
maybeElimOn = rotateR maybeElim

whenNothing :: a -> Maybe a -> a
whenNothing x Nothing = x
whenNothing _ (Just x) = x

-- }}}

-- List {{{

instance Functorial Eq [] where functorial = W
instance Functorial Ord [] where functorial = W

instance Iterable a [a] where
  foldl _ i [] = i
  foldl f i (x:xs) = let i' = f x i in i' `seq` foldl f i' xs
  foldlk _ i [] = i
  foldlk f i (x:xs) = f x i $ \ i' -> i' `seq` foldlk f i' xs
  foldr _ i [] = i
  foldr f i (x:xs) = f x $ foldr f i xs
instance (Eq a) => Container a [a] where
  (?) = flip isElem
instance Indexed Integer a [a] where
  (#) = flip elemAtN
instance Monoid [a] where
  null = []
  xs ++ ys = foldr (:) ys xs
instance Functorial Monoid [] where functorial = W
instance Unit [] where
  unit = (:[])
instance ListLike a [a] where
  nil = []
  cons = (:)
  uncons = coerce consL
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
instance MonadConcat [] where
  (<++>) = (++)
instance Functor [] where
  map _ [] = []
  map f (x:xs) = f x:map f xs
instance FunctorM [] where
  mapM _ [] = return []
  mapM f (x:xs) = do
    y <- f x
    ys <- mapM f xs
    return $ y:ys

nilL :: Prism [a] ()
nilL = Prism
  { coerce = \ xs -> case xs of
      [] -> Just ()
      _:_ -> Nothing
  , inject = \ () -> []
  }
consL :: Prism [a] (a,[a])
consL = Prism
  { coerce = \ xs -> case xs of
      [] -> Nothing
      x:xs' -> Just (x,xs')
  , inject = uncurry (:)
  }

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

-- }}}

-- Set {{{

data Set a where
  EmptySet :: Set a
  Set :: (Ord a) => Set.Set a -> Set a

instance Container a (Set a) where
  EmptySet ? _ = False
  Set s ? e = Set.member e s
instance Iterable a (Set a) where
  foldl _ i EmptySet = i
  foldl f i (Set s) = Set.foldl' (flip f) i s
  foldr _ i EmptySet = i
  foldr f i (Set s) = Set.foldr' f i s
instance Eq (Set a) where
  s1 == s2 = (s1 <= s2) /\ (s2 <= s1)
instance Ord (Set a) where
  EmptySet <= _ = True
  _ <= EmptySet = False
  Set s1 <= Set s2 = s1 <= s2
instance PartialOrder (Set a) where
  s1 <~ s2 = iterOn s1 True $ \ e -> (/\) $ s2 ? e
instance SetLike a (Set a) where
  learnSet EmptySet i _ = i
  learnSet (Set _) _ b = b
  empty = EmptySet
  isEmpty EmptySet = True
  isEmpty (Set s) = Set.null s
  insert e EmptySet = Set $ Set.singleton e
  insert e (Set s) = Set $ Set.insert e s
  remove EmptySet = Nothing
  remove (Set s) = map (mapSnd Set) $ Set.minView s
instance Bind Set where
  aM >>= k = joins $ map k $ fromSet aM
instance MonadZero Set where
  mzero = empty
instance MonadPlus Set where
  (<+>) = union
instance MonadConcat Set where
  (<++>) = union
instance JoinLattice (Set a) where
  bot = empty
  (\/) = union
instance Monoid (Set a) where
  null = empty
  (++) = union

setTranspose :: Set (Set a) -> Set (Set a)
setTranspose aMM = loop $ fromSet aMM
  where
    loop :: [(Set a)] -> Set (Set a)
    loop [] = EmptySet
    loop (s:ss) = 
      learnSet s (loop ss) $
      toSet $ map toSet $ transpose $ map fromSet $ s:ss

-- }}}

-- ListSet {{{

newtype ListSet a = ListSet { runListSet :: [a] }
  deriving (Monoid, Unit, Functor, Product, Applicative, Bind, Monad, Iterable a, Container a)
instance JoinLattice (ListSet a) where
  bot = ListSet []
  xs1 \/ xs2 = ListSet $ runListSet xs1 ++ runListSet xs2
instance MonadPlus ListSet where
  (<+>) = (\/)

-- }}}

-- Map {{{

data Map k v where
  EmptyMap :: Map k v
  Map :: (Ord k) => Map.Map k v -> Map k v

instance (Eq k, Eq v) => Eq (Map k v) where
  EmptyMap == EmptyMap = True
  EmptyMap == Map m = Map.null m
  Map m == EmptyMap = Map.null m
  Map m1 == Map m2 = m1 == m2
instance (Ord k, Ord v) => Ord (Map k v) where
  EmptyMap <= _ = True
  _ <= EmptyMap = False
  Map m1 <= Map m2 = m1 <= m2
instance (Ord k, PartialOrder v) => PartialOrder (Map k v) where
  m1 <~ m2 = iter (\ (k,v) -> (/\) $ maybeElim False (v <~) $ m2 # k) True m1
instance Indexed k v (Map k v) where
  EmptyMap # _ = Nothing
  Map m # k = Map.lookup k m
instance (Eq v) => Container (k, v) (Map k v) where
  m ? (k,v) = case m # k of
    Nothing -> False
    Just v' 
      | v == v' -> True
      | otherwise -> False
  
instance Iterable (k, v) (Map k v) where
  foldl _ i EmptyMap = i
  foldl f i (Map m) = Map.foldlWithKey' (rotateR $ curry f) i m
  foldr _ i EmptyMap = i
  foldr f i (Map m) = Map.foldrWithKey' (curry f) i m
instance MapLike k v (Map k v) where
  learnMap EmptyMap i _ = i
  learnMap (Map _) _ f = f
  mapEmpty = EmptyMap
  mapIsEmpty EmptyMap = True
  mapIsEmpty (Map m) = Map.null m
  mapInsertWith _ k v EmptyMap = Map $ Map.singleton k v
  mapInsertWith f k v (Map m) = Map $ Map.insertWith (flip f) k v m
  mapRemove EmptyMap = Nothing
  mapRemove (Map m) = map (mapSnd Map) $ Map.minViewWithKey m
instance (Eq v, JoinLattice v) => JoinLattice (Map k v) where
  bot = mapEmpty
  (\/) = mapUnionWith (\/)

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
