module FP.Core 

-- Exports  {{{

  ( module Prelude
  , module FP.Core
  , module GHC.Exts
  , module Data.Char
  , module Language.Haskell.TH
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
import Language.Haskell.TH (Q)
import Data.Char (isSpace, isAlphaNum, isLetter, isDigit)

-- }}}

-- Precedence {{{

infix  9 ?
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
infixr 9 .:
infixr 9 ..:
infixr 9 :.:

infix  7 /
infix  7 //
infixr 7 *
infixr 7 <*>
infixr 7 /\

infix  6 -
infix  6 \-\
infixr 6 +
infixr 6 ++
infixr 6 :+:
infixr 6 <+>
infixr 6 \/

infix  4 ⊑
infix  4 ⊏

infixl 1 >>=
infixl 1 >>
infixr 1 ~>

infixr 0 *$
infixr 0 ^$
infixr 0 ^*$
infixr 0 <$>

infixr 0 ~:
infixr 0 =:
infixr 0 |:

-- }}}

-- Basic Types {{{

data P a = P
data W (c :: Constraint) where W :: (c) => W c
with :: W c -> (c => a) -> a ; with W x = x

-- }}}

-------------
-- Classes --
-------------

-- Constraint  {{{

class    Universal a
instance Universal a

class    (c1 a, c2 a) => (c1 ::*:: c2) a
instance (c1 a, c2 a) => (c1 ::*:: c2) a

class    (t (u a)) => (t ::.:: u) a
instance (t (u a)) => (t ::.:: u) a

class c1 ::=>:: c2     where impl         :: (c1)       => W c2
class Functorial   c t where functorial   :: (c a)      => W (c (t a))
class Bifunctorial c t where bifunctorial :: (c a, c b) => W (c (t a b))

-- }}}

-- Conversion {{{

class ToInteger    a where toInteger    :: a        -> Integer
class FromInteger  a where fromInteger  :: Integer  -> a
class ToInt        a where toInt        :: a        -> Int
class FromInt      a where fromInt      :: Int      -> a
class ToRational   a where toRational   :: a        -> Rational
class FromRational a where fromRational :: Rational -> a
class ToDouble     a where toDouble     :: a        -> Double
class FromDouble   a where fromDouble   :: Double   -> a
class ToString     a where toString     :: a        -> String

-- }}}

-- Arithmetic {{{

class Peano a where
  zer :: a
  suc :: a -> a

piter :: (Eq a, Peano a) => (b -> b) -> b -> a -> b
piter f i0 x = loop i0 zer
  where
    loop i j
      | j == x = i
      | otherwise = 
        let i' = f i
        in i' `seq` loop i' $ suc j

piterOn :: (Eq a, Peano a) => a -> b -> (b -> b) -> b
piterOn = mirror piter

class (Peano a)          => Additive          a where { zero :: a ; (+) :: a -> a -> a }
class (Additive a)       => Subtractive       a where (-) :: a -> a -> a
class (Additive a)       => Multiplicative    a where { one :: a ; (*) :: a -> a -> a }
class (Multiplicative a) => Divisible         a where (/) :: a -> a -> a
class (Multiplicative a) => TruncateDivisible a where (//) :: a -> a -> a

class (TruncateDivisible a,ToInteger a,FromInteger a,ToInt a,FromInt a,ToRational a,ToDouble a) => Integral a
class (Divisible a,ToRational a,FromRational a,ToDouble a,FromDouble a,FromInteger a,FromInt a) => Fractional a

negate  :: (Subtractive a) => a -> a ; negate x  = zero - x
inverse :: (Divisible a)   => a -> a ; inverse x = one / x

-- }}}

-- PartialOrder {{{

data POrdering = PEQ | PLT | PGT | PUN

-- Minimal definition: pcompare OR (⊑)
class PartialOrder a where
  pcompare :: a -> a -> POrdering
  pcompare x y = case (x ⊑ y, y ⊑ x) of
    (True , True ) -> PEQ
    (True , False) -> PLT
    (False, True ) -> PGT
    (False, False) -> PUN
  (⊑) :: a -> a -> Bool
  x ⊑ y = case pcompare x y of
    PLT -> True
    PEQ -> True
    _   -> False
  (⊏) :: a -> a -> Bool
  x ⊏ y = case pcompare x y of
    PLT -> True
    _ -> False

(⋚) :: (Ord a)          => a -> a -> Ordering  ; (⋚) = compare
(⋈) :: (PartialOrder a) => a -> a -> POrdering ; (⋈) = pcompare
(⊒) :: (PartialOrder a) => a -> a -> Bool      ; (⊒) = flip (⊑)
(⊐) :: (PartialOrder a) => a -> a -> Bool      ; (⊐) = flip (⊏)

fromOrdering :: Ordering -> POrdering
fromOrdering EQ = PEQ
fromOrdering LT = PLT
fromOrdering GT = PGT

discreteOrder :: (Eq a) => a -> a -> POrdering
discreteOrder x y = if x == y then PEQ else PUN

findMax :: (Iterable a t, PartialOrder b) => (a -> b) -> a -> t -> a
findMax p i0 = iterFrom i0 $ \ a i -> if p a ⊐ p i then a else i

findMaxFrom :: (Iterable a t, PartialOrder b) => a -> (a -> b) -> t -> a
findMaxFrom = flip findMax

-- this only terminates if f is monotonic and there are no infinite ascending
-- chains for the lattice a
poiter :: (PartialOrder a) => (a -> a) -> a -> a
poiter f = loop
  where
    loop x =
      let x' = f x
      in if x' ⊑ x then x else loop x'

-- }}}

-- Category {{{

class Category t where
  catid :: t a a
  (<.>) :: t b c -> t a b -> t a c

type m ~>  n = forall a. m a -> n a
type t ~~> u = forall m. t m ~> u m

class Morphism  a b where morph  :: a ->  b
class Morphism2 m n where morph2 :: m ~>  n
class Morphism3 t u where morph3 :: t ~~> u

class (Morphism a b, Morphism b a) => Isomorphism a b
isoto   :: (Isomorphism a b) => a -> b ; isoto   = morph
isofrom :: (Isomorphism a b) => b -> a ; isofrom = morph

class (Morphism2 t u, Morphism2 u t) => Isomorphism2 t u
isoto2   :: (Isomorphism2 t u) => t ~> u                     ; isoto2   = morph2
isofrom2 :: (Isomorphism2 t u) => u ~> t                     ; isofrom2 = morph2
onIso2   :: (Isomorphism2 t u) => (u a -> u b) -> t a -> t b ; onIso2 f = isofrom2 . f . isoto2

class (Morphism3 v w, Morphism3 w v) => Isomorphism3 v w
isoto3   :: (Isomorphism3 v w) => v ~~> w ; isoto3   = morph3
isofrom3 :: (Isomorphism3 v w) => w ~~> v ; isofrom3 = morph3

-- }}}

-- Monoid {{{

class Monoid a where
  null :: a
  (++) :: a -> a -> a

iterAppend :: (Monoid a, Eq n, Peano n) => n -> a -> a ; iterAppend n = piterOn n null . (++)
concat     :: (Iterable a t, Monoid a)  => t -> a      ; concat       = foldr (++) null

-- }}}

-- Lattice  {{{

class Bot  a where bot  :: a
class Join a where (\/) :: a -> a -> a
class Top  a where top  :: a
class Meet a where (/\) :: a -> a -> a
class Neg a  where neg :: a -> a
class (Bot a, Join a) => JoinLattice a
class (Top a, Meet a) => MeetLattice a
class (JoinLattice a, MeetLattice a) => Lattice a
class (Lattice a, Neg a) => NegLattice a
  
joins :: (Iterable a t, JoinLattice a) => t -> a ; joins = iter (\/) bot
meets :: (Iterable a t, MeetLattice a) => t -> a ; meets = iter (/\) top

collect :: (Join a, PartialOrder a) => (a -> a) -> a -> a
collect f = poiter $ \ x -> x \/ f x

collectN :: (Join a, PartialOrder a, Eq n, Peano n) => n -> (a -> a) -> a -> a
collectN n f x0 = piterOn n x0 $ \ x -> x \/ f x

-- }}}

-- Functors {{{

class Commute t u where commute :: t (u a)  -> u (t a)
class Unit (t :: * -> *) where unit :: a -> t a
class Functor (t :: * -> *) where map :: (a -> b) -> (t a -> t b)

mapOn  :: (Functor t)            => t a -> (a -> b) -> t b                                 ; mapOn    = flip map
(^@)   :: (Functor t)            => (a -> b) -> t a -> t b                                 ; (^@)     = map
(^$)   :: (Functor t)            => (a -> b) -> t a -> t b                                 ; (^$)     = map
(^.)   :: (Functor t)            => (b -> c) -> (a -> t b) -> a -> t c                     ; g ^.   f = map g . f
(.^)   :: (Functor t)            => (t b -> c) -> (a -> b) -> t a -> c                     ; g .^   f = g . map f
(^.:)  :: (Functor t)            => (c -> d) -> (a -> b -> t c) -> a -> b -> t d           ; g ^.:  f = map g .: f
(^..:) :: (Functor t)            => (d -> e) -> (a -> b -> c -> t d) -> a -> b -> c -> t e ; g ^..: f = map g ..: f
(^^.)  :: (Functor t, Functor u) => (b -> c) -> (a -> t (u b)) -> a -> (t (u c))           ; g ^^.  f = map (map g) . f

class FunctorM (t :: * -> *) where mapM :: (Monad m) => (a -> m b) -> t a -> m (t b)

mapOnM   :: (FunctorM t, Monad m) => t a -> (a -> m b) -> m (t b)               ; mapOnM       = flip mapM
sequence :: (FunctorM t, Monad m) => t (m a) -> m (t a)                         ; sequence     = mapM id
(^*@)    :: (FunctorM t, Monad m) => (a -> m b) -> t a -> m (t b)               ; (^*@)        = mapM
(^*$)    :: (FunctorM t, Monad m) => (a -> m b) -> t a -> m (t b)               ; (^*$)        = mapM
(^*.)    :: (FunctorM t, Monad m) => (b -> m c) -> (a -> m b) -> t a -> m (t c) ; (g ^*. f) aT = mapM g *$ f ^*$ aT

class (Unit t, Functor t) => Applicative (t :: * -> *) where (<@>) :: t (a -> b) -> t a -> t b

pure  :: (Applicative t) => a -> t a                 ; pure  = unit
(<$>) :: (Applicative t) => t (a -> b) -> t a -> t b ; (<$>) = (<@>)
apair :: (Applicative t) => t a -> t b -> t (a, b)   ; apair aA bA = pure (,) <@> aA <@> bA

class                            Product (t :: * -> *) where (<*>) :: t a -> t b -> t (a, b)
class (Product m)             => Bind    (m :: * -> *) where (>>=) :: m a -> (a -> m b) -> m b
class (Applicative m, Bind m) => Monad   (m :: * -> *)

fail    ::                Chars -> m a                           ; fail       = Prelude.error
return  :: (Monad m)   => a -> m a                               ; return     = pure
kleisli :: (Monad m)   => (a -> b) -> (a -> m b)                 ; kleisli    = (.) return
(>>)    :: (Bind m)    => m a -> m b -> m b                      ; aM >> bM   = aM >>= const bM
extend  :: (Bind m)    => (a -> m b) -> (m a -> m b)             ; extend     = flip (>>=)
void    :: (Functor m) => m a -> m ()                            ; void       = map (const ())
(*@)    :: (Bind m)    => (a -> m b) -> (m a -> m b)             ; (*@)       = extend
(*$)    :: (Bind m)    => (a -> m b) -> (m a -> m b)             ; (*$)       = extend
(*.)    :: (Bind m)    => (b -> m c) -> (a -> m b) -> (a -> m c) ; (g *. f) x = g *$ f x
mjoin   :: (Bind m)    => m (m a) -> m a                         ; mjoin      = extend id
mmap    :: (Monad m)   => (a -> b) -> m a -> m b                 ; mmap f aM  = return . f *$ aM

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

when :: (Monad m) => Bool -> m () -> m ()
when True = id
when False = const $ return ()

traverse :: (Iterable a t, Monad m) => (a -> m ()) -> t -> m ()
traverse f = foldl (\ m a -> m >> f a) $ return ()

traverseOn :: (Iterable a t, Monad m)      => t -> (a -> m ()) -> m () ; traverseOn = flip traverse
exec       :: (Iterable (m ()) t, Monad m) => t -> m ()                ; exec       = traverse id

-- }}}

-- Monad Transformers {{{

class Unit2       (t :: (* -> *) -> (* -> *)) where unit2   :: m                ~> t m
class Join2       (t :: (* -> *) -> (* -> *)) where join2   :: t (t m)          ~> t m
class Functor2    (t :: (* -> *) -> (* -> *)) where map2    :: (m ~> n)         -> (t m ~> t n)
class IsoFunctor2 (t :: (* -> *) -> (* -> *)) where isoMap2 :: (m ~> n, n ~> m) -> (t m ~> t n)

class FunctorUnit2       (t :: (* -> *) -> (* -> *)) where funit2   :: (Functor m)            => m                ~> t m
class FunctorJoin2       (t :: (* -> *) -> (* -> *)) where fjoin2   :: (Functor m)            => t (t m)          ~> t m
class FunctorFunctor2    (t :: (* -> *) -> (* -> *)) where fmap2    :: (Functor m, Functor n) => (m ~> n)         -> (t m ~> t n)
class FunctorIsoFunctor2 (t :: (* -> *) -> (* -> *)) where fisoMap2 :: (Functor m, Functor n) => (m ~> n, n ~> m) -> (t m ~> t n)

class MonadUnit2       (t :: (* -> *) -> (* -> *)) where munit2   :: (Monad m)          => m                ~> t m
class MonadJoin2       (t :: (* -> *) -> (* -> *)) where mjoin2   :: (Monad m)          => t (t m)          ~> t m
class MonadFunctor2    (t :: (* -> *) -> (* -> *)) where mmap2    :: (Monad m, Monad n) => (m ~> n)         -> (t m ~> t n)
class MonadIsoFunctor2 (t :: (* -> *) -> (* -> *)) where misoMap2 :: (Monad m, Monad n) => (m ~> n, n ~> m) -> (t m ~> t n)

class MonadIO m where liftIO :: IO ~> m
class MonadQ  m where liftQ  :: Q ~> m

-- }}}

-- MonadMonoid {{{

class MonadBot (m :: * -> *) where mbot :: m a
class MonadTop (m :: * -> *) where mtop :: m a

class (MonadBot m) => MonadAppend (m :: * -> *) where (<++>) :: m a -> m a -> m a
class (MonadBot m) => MonadPlus   (m :: * -> *) where (<+>)  :: m a -> m a -> m a

guard :: (Monad m, MonadBot m) => Bool -> m ()
guard True = return ()
guard False = mbot

maybeZero :: (Monad m, MonadBot m) => Maybe a -> m a
maybeZero Nothing = mbot
maybeZero (Just a) = return a

mconcat :: (Iterable (m a) t, MonadAppend m) => t -> m a
mconcat = foldr (<++>) mbot

mlist :: (Iterable a t, Monad m, MonadAppend m) => t -> m a
mlist = foldr ((<++>) . return) mbot

msum :: (Iterable (m a) t, MonadPlus m) => t -> m a
msum = iter (<+>) mbot

mset :: (Iterable a t, Monad m, MonadPlus m) => t -> m a
mset = iter ((<+>) . return) mbot

many :: (Monad m, MonadAppend m) => m a -> m [a]
many aM = mconcat
  [ oneOrMoreList aM
  , return []
  ]

oneOrMore :: (Monad m, MonadAppend m) => m a -> m (a, [a])
oneOrMore aM = do
  x <- aM
  xs <- many aM
  return (x, xs)

twoOrMore :: (Monad m, MonadAppend m) => m a -> m (a, a, [a])
twoOrMore aM = do
  x1 <- aM
  (x2, xs) <- oneOrMore aM
  return (x1, x2, xs)

oneOrMoreList :: (Monad m, MonadAppend m) => m a -> m [a]
oneOrMoreList = uncurry (:) ^. oneOrMore

-- }}}

-- MonadMaybe {{{

newtype MaybeT m a = MaybeT { unMaybeT :: m (Maybe a) }
class MonadMaybe (m :: * -> *) where
  maybeI :: m ~> MaybeT m
  maybeE :: MaybeT m ~> m

obsMaybe :: (MonadMaybe m)                            => m a -> m (Maybe a) ; obsMaybe = unMaybeT . maybeI
effMaybe :: (MonadMaybe m)                            => m (Maybe a) -> m a ; effMaybe = maybeE . MaybeT
abort    :: (Monad m, MonadMaybe m)                   => m a                ; abort    = effMaybe $ return Nothing
mtry     :: (Monad m, MonadMaybe m, Iterable (m a) t) => t -> m a           ; mtry     = foldr (<|>) abort

(<|>) :: (Monad m, MonadMaybe m) => m a -> m a -> m a
aM1 <|> aM2 = do
  aM' <- obsMaybe aM1
  case aM' of
    Just a -> return a
    Nothing -> aM2

-- }}}

-- MonadError {{{

newtype ErrorT e m a = ErrorT { unErrorT :: m (e :+: a) }
class MonadError e (m :: * -> *) | m -> e where
  errorI :: m ~> ErrorT e m
  errorE :: ErrorT e m ~> m

obsError :: (MonadError e m)          => m a -> m (e :+: a) ; obsError = unErrorT . errorI
effError :: (MonadError e m)          => m (e :+: a) -> m a ; effError = errorE . ErrorT
sumError :: (Monad m, MonadError e m) => e :+: a -> m a     ; sumError = effError . return
throw    :: (Monad m, MonadError e m) => e -> m a           ; throw e  = sumError $ Inl e

catch :: (Monad m, MonadError e m) => m a -> (e -> m a) -> m a
catch aM h = do
  aeM <- unErrorT $ errorI aM
  case aeM of
    Inl e -> h e
    Inr a -> return a

-- }}}

-- MonadReader {{{

newtype ReaderT r m a = ReaderT { unReaderT :: r -> m a }
class MonadReader r (m :: * -> *) | m -> r where
  readerI :: m ~> ReaderT r m
  readerE :: ReaderT r m ~> m

runReaderT ::                               r -> ReaderT r m a -> m a          ; runReaderT  = flip unReaderT
obsReader  :: (MonadReader r m)          => m a -> (r -> m a)                  ; obsReader   = unReaderT . readerI
effReader  :: (MonadReader r m)          => (r -> m a) -> m a                  ; effReader   = readerE . ReaderT
ask        :: (Monad m, MonadReader r m) => m r                                ; ask         = effReader return
local      :: (MonadReader r m)          => (r -> r) -> m a -> m a             ; local f aM  = effReader $ obsReader aM . f
localSet   :: (MonadReader r m)          => r -> m a -> m a                    ; localSet    = local . const
askL       :: (Monad m, MonadReader r m) => Lens r a -> m a                    ; askL l      = access l ^$ ask
localL     :: (MonadReader r m)          => Lens r b -> (b -> b) -> m a -> m a ; localL      = local .: update
localSetL  :: (MonadReader r m)          => Lens r b -> b -> m a -> m a        ; localSetL l = localL l . const

-- }}}

-- MonadWriter {{{

newtype WriterT o m a = WriterT { unWriterT :: m (o, a) }
class MonadWriter o m | m -> o where
  writerI :: m ~> WriterT o m
  writerE :: WriterT o m ~> m

obsWriter :: (MonadWriter o m)          => m a -> m (o, a) ; obsWriter = unWriterT . writerI
effWriter :: (MonadWriter o m)          => m (o, a) -> m a ; effWriter = writerE . WriterT
tell      :: (Monad m, MonadWriter o m) => o -> m ()       ; tell      = effWriter . return . (,())
hijack    :: (MonadWriter o m)          => m a -> m (o, a) ; hijack    = obsWriter

-- }}}

-- MonadState {{{

newtype StateT s m a = StateT { unStateT :: s -> m (s, a) }
class MonadState s m | m -> s where
  stateI :: m ~> StateT s m
  stateE :: StateT s m ~> m

obsState :: (MonadState s m)          => m a -> (s -> m (s, a))         ; obsState  = unStateT . stateI
effState :: (MonadState s m)          => (s -> m (s, a)) -> m a         ; effState  = stateE . StateT
get      :: (Monad m, MonadState s m) => m s                            ; get       = stateE $ StateT $ \ s -> return (s, s)
put      :: (Monad m, MonadState s m) => s -> m ()                      ; put s     = stateE $ StateT $ \ _ -> return (s, ())
modify   :: (Monad m, MonadState s m) => (s -> s) -> m ()               ; modify    = modifyM . kleisli
modifyM  :: (Monad m, MonadState s m) => (s -> m s) -> m ()             ; modifyM f = stateE $ StateT $ \ s -> f s <*> return ()
getL     :: (Monad m, MonadState s m) => Lens s a -> m a                ; getL l    = map (access l) get
putL     :: (Monad m, MonadState s m) => Lens s a -> a -> m ()          ; putL      = modify .: set
modifyL  :: (Monad m, MonadState s m) => Lens s a -> (a -> a) -> m ()   ; modifyL   = modify .: update
modifyLM :: (Monad m, MonadState s m) => Lens s a -> (a -> m a) -> m () ; modifyLM  = modifyM .: updateM

next :: (Monad m, MonadState s m, Peano s) => m s
next = do
  i <- get
  put $ suc i
  return i

nextL :: (Monad m, MonadState s m, Peano a) => Lens s a -> m a
nextL l = do
  i <- getL l
  putL l $ suc i
  return i

bumpL :: (Monad m, MonadState s m, Peano a) => Lens s a -> m ()
bumpL l = modifyL l suc

-- }}}

-- MonadRWST {{{

newtype RWST r o s m a = RWST { unRWST :: ReaderT r (WriterT o (StateT s m)) a }
class (MonadReader r m, MonadWriter o m, MonadState s m) => MonadRWS r o s m where
  rwsI :: m ~> RWST r o s m
  rwsE :: RWST r o s m ~> m

-- }}}

-- MonadCont {{{

newtype ContT r m a = ContT { unContT :: (a -> m r) -> m r }
class MonadCont r m | m -> r where
  contI :: m ~> ContT r m
  contE :: ContT r m ~> m

obsCont :: (MonadCont r m) => m a -> ((a -> m r) -> m r)          ; obsCont      = unContT . contI
effCont :: (MonadCont r m) => ((a -> m r) -> m r) -> m a          ; effCont      = contE . ContT
callCC  :: (MonadCont r m) => ((a -> m r) -> m r) -> m a          ; callCC       = effCont
withC   :: (MonadCont r m) => (a -> m r) -> m a -> m r            ; withC        = flip obsCont
reset   :: (Monad m, MonadCont r m) => m r -> m r                 ; reset aM     = callCC $ \ k -> k *$ withC return aM
modifyC :: (Monad m, MonadCont r m) => (r -> m r) -> m a -> m a   ; modifyC f aM = callCC $ \ k -> withC (f *. k) aM

-- }}}

-- MonadOpaqueCont {{{

newtype OpaqueContT k r m a = OpaqueContT { unOpaqueContT :: k r m a -> m r }
class MonadOpaqueCont k r m | m -> k, m -> r where
  opaqueContI :: m ~> OpaqueContT k r m
  opaqueContE :: OpaqueContT k r m ~> m

obsOpaqueCont :: (MonadOpaqueCont k r m) => m a -> (k r m a -> m r) ; obsOpaqueCont = unOpaqueContT . opaqueContI
effOpaqueCont :: (MonadOpaqueCont k r m) => (k r m a -> m r) -> m a ; effOpaqueCont = opaqueContE . OpaqueContT
opaqueWithC   :: (MonadOpaqueCont k r m) => k r m a -> m a -> m r   ; opaqueWithC  = flip obsOpaqueCont
opaqueCallCC  :: (MonadOpaqueCont k r m) => (k r m a -> m r) -> m a ; opaqueCallCC = effOpaqueCont

-- }}}

-- Observing and eliminating containers {{{

class Container e t | t -> e where
  (?) :: t -> e -> Bool

elem :: (Container e t) => e -> t -> Bool
elem = flip (?)

class Indexed k v t | t -> k, t -> v where
  (#) :: t -> k -> Maybe v

index :: (Indexed k v t) => t -> k -> Maybe v
index = (#)

(#!) :: (Indexed k v t) => t -> k -> v
(#!) = unsafe_coerce justL .: (#)

lookup :: (Indexed k v t) => k -> t -> Maybe v
lookup = flip (#)

class Iterable a t | t -> a where
  -- the left fold, exposing the fold continuation
  foldlk :: (b -> a -> (b -> b) -> b) -> b -> t -> b
  foldlk f i0 t = foldl (\ (iK :: (b -> b) -> b) (a :: a) (k :: b -> b) ->
    iK $ \ i -> f i a k) ($ i0) t id
  -- the left fold
  foldl :: (b -> a -> b) -> b -> t -> b
  foldl f = foldlk $ \ i a k -> let i' = f i a in i' `seq` k i'
  -- the right fold
  foldr :: (a -> b -> b) -> b -> t -> b
  foldr f = foldlk $ \ i a k -> f a $ k i
  -- the most efficient fold (unspecified order)
  iter :: (a -> b -> b) -> b -> t -> b
  iter = foldl . flip
  size :: (Integral n) => t -> n
  size = iter (const suc) 0

foldlOn   :: (Iterable a t) => t -> b -> (b -> a -> b) -> b ; foldlOn   = mirror foldl
foldlFrom :: (Iterable a t) => b -> (b -> a -> b) -> t -> b ; foldlFrom = flip foldl
foldrOn   :: (Iterable a t) => t -> b -> (a -> b -> b) -> b ; foldrOn   = mirror foldr
foldrFrom :: (Iterable a t) => b -> (a -> b -> b) -> t -> b ; foldrFrom = flip foldr
iterOn    :: (Iterable a t) => t -> b -> (a -> b -> b) -> b ; iterOn    = mirror iter
iterFrom  :: (Iterable a t) => b -> (a -> b -> b) -> t -> b ; iterFrom  = flip iter

isElem :: (Iterable a t, Eq a) => a -> t -> Bool
isElem x = foldlk (\ _ x' k -> if x == x' then True else k False) False

elemAtN :: (Iterable a t, Peano n, Eq n) => n -> t -> Maybe a
elemAtN n t = case foldlk ff (Inr zer) t of
  Inl x -> Just x
  Inr _ -> Nothing
  where
    ff (Inr i) x' k = if i == n then Inl x' else k $ Inr $ suc i
    ff (Inl _) _ _ = error "internal error"

toList :: (Iterable a t)             => t -> [a]     ; toList = foldr (:) []
toSet  :: (Ord a, Iterable a t)      => t -> Set a   ; toSet  = foldr insert empty
toMap  :: (Ord k, Iterable (k, v) t) => t -> Map k v ; toMap  = foldr (uncurry mapInsert) mapEmpty

-- }}}

-- Creating containers {{{

class Buildable a t | t -> a where { nil :: t ; (&) :: a -> t -> t }

build  :: (Buildable a t) => [a] -> t ; build  = foldr (&) nil
single :: (Buildable a t) => a -> t   ; single = flip  (&) nil

filter :: (Iterable a t, Buildable a t) => (a -> Bool) -> t -> t
filter p = foldrFrom nil $ \ x -> if p x then (x &) else id

reverse :: (Iterable a t, Buildable a t) => t -> t
reverse = foldlFrom nil $ flip (&)

uniques :: (Eq a, Iterable a t, Buildable a t) => t -> t
uniques = foldrFrom nil $ \ x xs -> x & filter ((/=) x) xs

replicate :: (Eq n, Peano n, Iterable a t, Buildable a t) => n -> a -> t
replicate n = piterOn n nil . (&)

fromList :: (Buildable a t) => [a] -> t          ; fromList = foldr (&) nil
fromSet  :: (Buildable a t) => Set a -> t        ; fromSet  = foldr (&) nil
fromMap  :: (Buildable (k, v) t) => Map k v -> t ; fromMap  = foldr (&) nil

-- }}}

----------
-- Data --
----------

-- Function {{{

applyTo :: a -> (a -> b) -> b ; applyTo = flip ($)

(.:)    :: (c -> d) -> (a -> b -> c)                -> (a -> b -> d)                ; (.:)    = (.) . (.)
(..:)   :: (d -> e) -> (a -> b -> c -> d)           -> (a -> b -> c -> e)           ; (..:)   = (.) . (.:)
(...:)  :: (e -> f) -> (a -> b -> c -> d -> e)      -> (a -> b -> c -> d -> f)      ; (...:)  = (.) . (..:)
(....:) :: (f -> g) -> (a -> b -> c -> d -> e -> f) -> (a -> b -> c -> d -> e -> g) ; (....:) = (.) . (...:)

rotateR     :: (a -> b -> c -> d) -> (c -> a -> b -> d)   ; rotateR f c a b = f a b c
rotateL     :: (a -> b -> c -> d) -> (b -> c -> a -> d)   ; rotateL f b c a = f a b c
mirror      :: (a -> b -> c -> d) -> (c -> b -> a -> d)   ; mirror f c b a  = f a b c
on          :: (b -> b -> c) -> (a -> b) -> (a -> a -> c) ; on p f x y      = p (f x) (f y)
composition :: [a -> a] -> a -> a                         ; composition     = unEndo . concat . map Endo

instance Category (->) where { catid = id ; (<.>) = (.) }
instance Functor ((->) a) where map = (.)
instance (Monoid b)      => Monoid (a -> b) where { null = const null ; (++) f g x = f x ++ g x }
instance (Bot b)         => Bot (a -> b) where bot = const bot
instance (Join b)        => Join (a -> b) where (f \/ g) x = f x \/ g x
instance (Top b)         => Top (a -> b) where top = const top
instance (Meet b)        => Meet (a -> b) where (f /\ g) x = f x /\ g x
instance (Neg b)         => Neg (a -> b) where neg f = neg . f
instance (JoinLattice b) => JoinLattice (a -> b)
instance (MeetLattice b) => MeetLattice (a -> b)
instance (Lattice b)     => Lattice (a -> b)
instance (NegLattice b)  => NegLattice (a -> b)

-- }}}

-- Endo {{{

data Endo a = Endo { unEndo :: a -> a }
runEndo :: a -> Endo a -> a ; runEndo = flip unEndo
instance Monoid (Endo a) where { null = Endo id ; g ++ f = Endo $ unEndo g . unEndo f }

data KleisliEndo m a = KleisliEndo { unKleisliEndo :: a -> m a }
runKleisliEndo :: a -> KleisliEndo m a -> m a ; runKleisliEndo = flip unKleisliEndo

instance (Monad m) => Monoid (KleisliEndo m a) where
  null = KleisliEndo return
  g ++ f = KleisliEndo $ unKleisliEndo g *. unKleisliEndo f

-- }}}

-- Bool {{{

ifThenElse :: Bool -> a -> a -> a               ; ifThenElse c x y = case c of { True -> x ; False -> y }
fif        :: Bool -> a -> a -> a               ; fif              = ifThenElse
cond       :: (a -> Bool) -> c -> c -> (a -> c) ; cond p t f x     = if p x then t else f

instance Bot Bool where bot = False
instance Join Bool where (\/) = (||)
instance Top Bool where top = True
instance Meet Bool where (/\) = (&&)
instance Monoid Bool where { null = bot ; (++) = (\/) }
instance ToString Bool where toString = show
instance JoinLattice Bool
instance MeetLattice Bool
instance Lattice Bool

-- }}}

-- Integer {{{

instance ToInteger         Integer where toInteger = id
instance FromInteger       Integer where fromInteger = id
instance ToInt             Integer where toInt = Prelude.fromIntegral
instance FromInt           Integer where fromInt = Prelude.fromIntegral
instance ToRational        Integer where toRational = Prelude.fromIntegral
instance ToDouble          Integer where toDouble = Prelude.fromIntegral
instance ToString          Integer where toString = show
instance Peano             Integer where { zer = 0 ; suc = Prelude.succ }
instance Additive          Integer where { zero = 0 ; (+) = (Prelude.+) }
instance Subtractive       Integer where (-) = (Prelude.-)
instance Multiplicative    Integer where { one = 1 ; (*) = (Prelude.*) }
instance TruncateDivisible Integer where (//) = Prelude.div
instance PartialOrder      Integer where pcompare = fromOrdering .: compare
instance Join              Integer where (\/) = Prelude.max
instance Meet              Integer where (/\) = Prelude.min
instance Neg               Integer where neg = negate
instance Monoid            Integer where { null = 0 ; (++) = (+) }
instance Integral          Integer

-- }}}

-- Int {{{

instance ToInteger         Int where toInteger = Prelude.toInteger
instance FromInteger       Int where fromInteger = Prelude.fromIntegral
instance ToInt             Int where toInt = id
instance FromInt           Int where fromInt = id
instance ToRational        Int where toRational = Prelude.fromIntegral
instance ToDouble          Int where toDouble = Prelude.fromIntegral
instance ToString          Int where toString = show
instance Peano             Int where { zer = 0 ; suc = Prelude.succ }
instance Additive          Int where { zero = 0 ; (+) = (Prelude.+) }
instance Subtractive       Int where (-) = (Prelude.-)
instance Multiplicative    Int where { one = 1 ; (*) = (Prelude.*) }
instance TruncateDivisible Int where (//) = Prelude.div
instance PartialOrder      Int where pcompare = fromOrdering .: compare
instance Bot               Int where bot = Prelude.minBound
instance Join              Int where (\/) = Prelude.max
instance Top               Int where top = Prelude.maxBound
instance Meet              Int where (/\) = Prelude.min
instance Neg               Int where neg = negate
instance Monoid            Int where { null = 0 ; (++) = (+) }
instance Integral          Int
instance JoinLattice       Int
instance MeetLattice       Int
instance Lattice           Int
instance NegLattice        Int

-- }}}

-- Rational {{{

instance FromInteger    Rational where fromInteger = Prelude.fromInteger
instance FromInt        Rational where fromInt = Prelude.fromIntegral
instance ToRational     Rational where toRational = id
instance FromRational   Rational where fromRational = id
instance ToDouble       Rational where toDouble = Prelude.fromRational
instance FromDouble     Rational where fromDouble = Prelude.toRational
instance ToString       Rational where toString = show
instance Peano          Rational where { zer = 0 ; suc = (1+) }
instance Additive       Rational where { zero = 0 ; (+) = (Prelude.+) }
instance Subtractive    Rational where (-) = (Prelude.-)
instance Multiplicative Rational where { one = 1 ; (*) = (Prelude.*) }
instance Divisible      Rational where (/) = (Prelude./)
instance PartialOrder   Rational where pcompare = fromOrdering .: compare
instance Join           Rational where (\/) = Prelude.max
instance Meet           Rational where (/\) = Prelude.min
instance Neg            Rational where neg = negate
instance Monoid         Rational where { null = 0 ; (++) = (+) }
instance Fractional     Rational

-- }}}

-- Double {{{

instance FromInteger    Double where fromInteger = Prelude.fromInteger
instance FromInt        Double where fromInt = Prelude.fromIntegral
instance ToRational     Double where toRational = Prelude.toRational
instance FromRational   Double where fromRational = Prelude.fromRational
instance ToDouble       Double where toDouble = id
instance FromDouble     Double where fromDouble = id
instance ToString       Double where toString = show
instance Peano          Double where { zer = 0 ; suc = (1+) }
instance Additive       Double where { zero = 0 ; (+) = (Prelude.+) }
instance Subtractive    Double where (-) = (Prelude.-)
instance Multiplicative Double where { one = 1 ; (*) = (Prelude.*) }
instance Divisible      Double where (/) = (Prelude./)
instance PartialOrder   Double where pcompare = fromOrdering .: compare
instance Join           Double where (\/) = Prelude.max
instance Meet           Double where (/\) = Prelude.min
instance Neg            Double where neg = negate
instance Monoid         Double where { null = 0 ; (++) = (+) }
instance Fractional     Double

-- }}}

-- String {{{


type String = Text
type Chars = [Char]

fromChars  :: Chars -> String                 ; fromChars  = Text.pack
fromString :: Chars -> String                 ; fromString = fromChars
toChars    :: String -> Chars                 ; toChars    = Text.unpack
error      :: String -> a                     ; error      = Prelude.error . toChars 
show       :: (Prelude.Show a) => a -> String ; show       = fromChars . Prelude.show
read       :: (Prelude.Read a) => String -> a ; read       = Prelude.read . toChars

instance ToString Char where toString = show
instance Monoid String where { null = Text.empty ; (++) = Text.append }
instance ToString String where toString = show
instance Container Char String where s ? c = isL justL $ Text.find (== c) s
instance Iterable Char String where
  foldl = Text.foldl'
  foldr = Text.foldr
  iter = foldl . flip
  size = fromInt . Text.length

-- }}}

-- Lens {{{

data Cursor a b = Cursor { focus :: a, construct :: a -> b }
data Lens a b = Lens { unLens :: a -> Cursor b a }

lens    :: (a -> b) -> (a -> b -> a) -> Lens a b           ; lens getter setter = Lens $ \ s -> Cursor (getter s) (setter s)
isoLens :: (a -> b) -> (b -> a)      -> Lens a b           ; isoLens to from    = lens to $ const from
update  :: Lens a b -> (b -> b) -> a -> a                  ; update l f a       = let Cursor b ba = unLens l a in ba $ f b
updateM :: (Monad m) => Lens a b -> (b -> m b) -> a -> m a ; updateM l f a      = let Cursor b ba = unLens l a in map ba $ f b
access  :: Lens a b -> a -> b                              ; access             = focus .: unLens
(~:)    :: Lens a b -> (b -> b) -> a -> a                  ; (~:)               = update
set     :: Lens a b -> b -> a -> a                         ; set l              = update l . const
(=:)    :: Lens a b -> b -> a -> a                         ; (=:)               = set
(|:)    :: a -> (a -> a) -> a                              ; (|:)               = applyTo

instance Category Lens where
  catid = isoLens id id
  g <.> f = Lens $ \ a -> 
    let Cursor b ba = unLens f a
        Cursor c cb = unLens g b
    in Cursor c $ ba . cb

-- }}}

-- Prism {{{

data Prism a b = Prism { inject :: b -> a, coerce :: a -> Maybe b }

prism         :: (b -> a) -> (a -> Maybe b) -> Prism a b ; prism            = Prism
isoPrism      :: (b -> a) -> (a -> b)       -> Prism a b ; isoPrism from to = prism from $ Just . to
unsafe_coerce :: Prism a b -> a -> b                     ; unsafe_coerce    = maybeElim (error "unsafe_coerce") id .: coerce
isL           :: Prism a b -> a -> Bool                  ; isL              = maybeElim False (const True) .: coerce
alter         :: Prism a b -> (b -> b) -> a -> a         ; alter p f a      = maybeElim a (inject p . f) $ coerce p a
(~^)          :: Prism a b -> (b -> b) -> a -> a         ; (~^)             = alter
pset          :: Prism a b -> b -> a -> a                ; pset p           = alter p . const

instance Category Prism where
  catid = isoPrism id id
  g <.> f = Prism
    { coerce = coerce g *. coerce f
    , inject = inject f . inject g
    }

-- }}}

-- Compose {{{

newtype (t :.: u) a = Compose { unCompose :: t (u a) }
  deriving (Eq, Ord, Bot, Join, JoinLattice, Top, Meet, MeetLattice, Lattice, PartialOrder)

onComposeIso :: (t (u a) -> t (u b)) -> (t :.: u) a -> (t :.: u) b ; onComposeIso f (Compose x) = Compose $ f x

instance (Functor t, Functor u) => Functor (t :.: u) where map = onComposeIso . map . map
instance (Functorial JoinLattice t, Functorial JoinLattice u) => Functorial JoinLattice (t :.: u) where
  functorial :: forall a. (JoinLattice a) => W (JoinLattice ((t :.: u) a))
  functorial =
    with (functorial :: W (JoinLattice (u a))) $
    with (functorial :: W (JoinLattice (t (u a)))) $
    W

-- Tuple {{{

swap   :: (a, b) -> (b, a)               ; swap (x, y)     = (y, x)
fstL   :: Lens (a, b) a                  ; fstL            = lens fst $ \ (_,b) -> (,b)
sndL   :: Lens (a, b) b                  ; sndL            = lens snd $ \ (a,_) -> (a,)
mapFst :: (a -> a') -> (a, b) -> (a', b) ; mapFst f (a, b) = (f a, b)
mapSnd :: (b -> b') -> (a, b) -> (a, b') ; mapSnd f (a, b) = (a, f b)

instance (PartialOrder a, PartialOrder b) => PartialOrder (a, b) where
  (a1, b1) ⊑ (a2, b2) = (a1 ⊑ a2) /\ (b1 ⊑ b2)
instance (PartialOrder a, PartialOrder b, PartialOrder c) => PartialOrder (a, b, c) where
  (a1, b1, c1) ⊑ (a2, b2, c2) = (a1 ⊑ a2) /\ (b1 ⊑ b2) /\ (c1 ⊑ c2)
instance (PartialOrder a, PartialOrder b, PartialOrder c, PartialOrder d, PartialOrder e) => PartialOrder (a, b, c, d, e) where
  (a1, b1, c1, d1, e1) ⊑ (a2, b2, c2, d2, e2) = (a1 ⊑ a2) /\ (b1 ⊑ b2) /\ (c1 ⊑ c2) /\ (d1 ⊑ d2) /\ (e1 ⊑ e2)
instance (Monoid a, Monoid b) => Monoid (a, b) where
  null = (null, null)
  (a1, b1) ++ (a2, b2) = (a1 ++ a2, b1 ++ b2)
instance (Bot a, Bot b) => Bot (a, b) where 
  bot = (bot, bot)
instance (Join a, Join b) => Join (a, b) where 
  (a1, b1) \/ (a2, b2) = (a1 \/ a2, b1 \/ b2)
instance (JoinLattice a, JoinLattice b) => JoinLattice (a, b)
instance (Bot a, Bot b, Bot c) => Bot (a, b, c) where 
  bot = (bot, bot, bot)
instance (Join a, Join b, Join c) => Join (a, b, c) where 
  (a1, b1, c1) \/ (a2, b2, c2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2)
instance (JoinLattice a, JoinLattice b, JoinLattice c) => JoinLattice (a, b, c)
instance (Bot a, Bot b, Bot c, Bot d, Bot e) => Bot (a, b, c, d, e) where 
  bot = (bot, bot, bot, bot, bot)
instance (Join a, Join b, Join c, Join d, Join e) => Join (a, b, c, d, e) where
  (a1, b1, c1, d1, e1) \/ (a2, b2, c2, d2, e2) = (a1 \/ a2, b1 \/ b2, c1 \/ c2, d1 \/ d2, e1 \/ e2)
instance (JoinLattice a, JoinLattice b, JoinLattice c, JoinLattice d, JoinLattice e) => JoinLattice (a, b, c, d, e)
instance (JoinLattice a) => Functorial JoinLattice ((,) a) where functorial = W
instance Bifunctorial Eq (,) where bifunctorial = W
instance Bifunctorial Ord (,) where bifunctorial = W

-- }}}

-- Sum {{{

data a :+: b = Inl a | Inr b deriving (Eq, Ord)

sumElim :: (a -> c) -> (b -> c) -> a :+: b -> c           ; sumElim f g = \case { Inl a -> f a ; Inr b -> g b }
inlL    :: Prism (a :+: b) a                              ; inlL       = Prism Inl $ sumElim Just $ const Nothing
inrL    :: Prism (a :+: b) b                              ; inrL       = Prism Inr $ sumElim (const Nothing) Just
mapInl  :: (a -> a') -> a :+: b -> a' :+: b               ; mapInl f   = sumElim (Inl . f) Inr
mapInr  :: (b -> b') -> a :+: b -> a :+: b'               ; mapInr f   = sumElim Inl $ Inr . f
mapSum  :: (a -> a') -> (b -> b') -> a :+: b -> a' :+: b' ; mapSum f g = sumElim (Inl . f) (Inr . g)

instance MonadError a ((:+:) a) where
  errorI :: a :+: b -> ErrorT a ((:+:) a) b
  errorI ab = ErrorT $ Inr ab
  errorE :: ErrorT a ((:+:) a) b -> a :+: b
  errorE aME = case unErrorT aME of
    Inl a -> Inl a
    Inr (Inl a) -> Inl a
    Inr (Inr b) -> Inr b

instance Unit ((:+:) a) where unit = Inr
instance Functor ((:+:) a) where map = mmap
instance Product ((:+:) a) where (<*>) = mpair
instance Applicative ((:+:) a) where (<@>) = mapply
instance Bind ((:+:) a) where abM >>= k = sumElim Inl k abM
instance Monad ((:+:) a)

-- }}}

-- }}}

-- Maybe {{{

maybeElim   :: b -> (a -> b) -> Maybe a -> b ; maybeElim i f = \case { Nothing -> i ; Just a -> f a }
nothingL    :: Prism (Maybe a) ()            ; nothingL      = prism (const Nothing) $ maybeElim (Just ()) $ const Nothing
justL       :: Prism (Maybe a) a             ; justL         = Prism Just id
maybeElimOn :: Maybe a -> b -> (a -> b) -> b ; maybeElimOn   = rotateR maybeElim
maybeNot    :: a -> Maybe a -> a             ; maybeNot x    = maybeElim x id

instance MonadMaybe Maybe where
  maybeI :: Maybe ~> MaybeT Maybe
  maybeI = MaybeT . Just
  maybeE :: MaybeT Maybe ~> Maybe
  maybeE aM = case unMaybeT aM of
    Nothing -> Nothing
    Just aM' -> aM'
instance Monoid (Maybe a) where
  null = Nothing
  Just x ++ _ = Just x
  Nothing ++ aM = aM

instance Bind Maybe where aM >>= k = maybeElim Nothing k aM
instance Unit Maybe where unit = Just
instance Functor Maybe where map = mmap
instance Applicative Maybe where (<@>) = mapply
instance Product Maybe where (<*>) = mpair
instance MonadBot Maybe where mbot = null
instance MonadAppend Maybe where (<++>) = (++)
instance Monad Maybe

-- }}}

-- List {{{

nilL    ::              Prism [a] ()          ; nilL    = Prism (const []) $ \case { [] -> Just () ; _:_ -> Nothing }
consL   ::              Prism [a] (a,[a])     ; consL   = Prism (uncurry (:)) $ \case { [] -> Nothing ; x:xs' -> Just (x,xs') }
singleL ::              Prism [a] a           ; singleL = Prism single $ \case { [a] -> Just a ; _ -> Nothing }
length  :: (Peano n) => [a] -> n              ; length  = foldl (const . suc) zer

mapHead :: (a -> a) -> [a] -> [a]
mapHead _ [] = []
mapHead f (x:xs) = f x:xs

mapTail :: (a -> a) -> [a] -> [a]
mapTail _ [] = []
mapTail f (x:xs) = x:map f xs

head :: [a] -> Maybe a
head [] = Nothing
head (x:_) = Just x

tail :: [a] -> Maybe [a]
tail [] = Nothing
tail (_:xs) = Just xs

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

bigProduct :: [[a]] -> [[a]]
bigProduct [] = [[]]
bigProduct (xs:xss) = do
  let xss' = bigProduct xss
  x <- xs
  map (x:) xss'


instance Iterable a [a] where
  foldl _ i [] = i
  foldl f i (x:xs) = let i' = f i x in i' `seq` foldl f i' xs
  foldlk _ i [] = i
  foldlk f i (x:xs) = f i x $ \ i' -> i' `seq` foldlk f i' xs
  foldr _ i [] = i
  foldr f i (x:xs) = f x $ foldr f i xs
instance (Eq k) => Indexed k v [(k, v)] where
  [] # _ = Nothing
  ((k,v):kvs) # k' | k == k' = Just v
                   | otherwise = kvs # k'
instance Bind [] where
  []     >>= _ = []
  (x:xs) >>= k = k x ++ (xs >>= k)
instance FunctorM [] where
  mapM _ [] = return []
  mapM f (x:xs) = do
    y <- f x
    ys <- mapM f xs
    return $ y:ys

instance (Eq a) => Container a [a] where (?) = flip isElem
instance Buildable a [a] where { nil = [] ; (&) = (:) }
instance Monoid [a] where { null = [] ; xs ++ ys = foldr (:) ys xs }
instance Unit [] where unit = (:[])
instance Functor [] where map f = foldr ((:) . f) []
instance Product [] where (<*>) = mpair
instance Applicative [] where (<@>) = mapply
instance MonadBot [] where mbot = []
instance MonadAppend [] where (<++>) = (++)
instance Functorial Monoid [] where functorial = W
instance Functorial Eq [] where functorial = W
instance Functorial Ord [] where functorial = W
instance Monad []

-- }}}

-- Set {{{

data Set a where
  EmptySet :: Set a
  Set :: (Ord a) => Set.Set a -> Set a

setPrimElim :: b -> ((Ord a) => Set.Set a -> b) -> Set a -> b
setPrimElim i f = \case { EmptySet -> i ; Set x -> f x }

setPrimElimOn :: Set a -> b -> ((Ord a) => Set.Set a -> b) -> b
setPrimElimOn = rotateR setPrimElim

setPrimElim2 :: b 
  -> ((Ord a) => Set.Set a -> b) 
  -> ((Ord a) => Set.Set a -> b) 
  -> ((Ord a) => Set.Set a -> Set.Set a -> b) 
  -> Set a -> Set a -> b
setPrimElim2 i f1 f2 ff s1 s2 = 
  setPrimElimOn s1 (setPrimElimOn s2 i f1) $ \ p1 -> 
    setPrimElimOn s2 (f2 p1) $ \ p2 -> 
      ff p1 p2

setPrimElim2' :: b -> ((Ord a) => Set.Set a -> b) -> ((Ord a) => Set.Set a -> Set.Set a -> b) -> Set a -> Set a -> b
setPrimElim2' i f = setPrimElim2 i f f

toPrimSet :: Set a -> Set.Set a
toPrimSet = setPrimElim Set.empty id

learnSet :: Set a -> b -> ((Ord a) => b) -> b 
learnSet s i f = setPrimElimOn s i $ const f

empty   :: Set a         ; empty   = EmptySet
isEmpty :: Set a -> Bool ; isEmpty = setPrimElim True Set.null

insert :: (Ord a) => a -> Set a -> Set a
insert e = setPrimElim (Set $ Set.singleton e) $ Set . Set.insert e

union :: Set a -> Set a -> Set a
union = setPrimElim2' EmptySet Set $ Set .: Set.union

intersection :: Set a -> Set a -> Set a
intersection = setPrimElim2' EmptySet (const EmptySet) $ Set .: Set.intersection

remove :: Set a -> Maybe (a, Set a)
remove = setPrimElim Nothing $ map (mapSnd Set) . Set.minView

(\-\) :: Set a -> Set a -> Set a
(\-\) = setPrimElim2 EmptySet (const EmptySet) Set $ Set .: (Set.\\)

setMap :: (Ord b) => (a -> b) -> Set a -> Set b
setMap f = setPrimElim EmptySet $ Set . Set.map f

maybeSet :: (Ord a) => Maybe a -> Set a
maybeSet = maybeElim empty single

setTranspose :: Set (Set a) -> Set (Set a)
setTranspose aMM = loop $ toList aMM
  where
    loop :: [(Set a)] -> Set (Set a)
    loop [] = EmptySet
    loop (s:ss) = 
      learnSet s (loop ss) $
      toSet $ map toSet $ transpose $ map toList $ s:ss

setBigProduct :: Set (Set a) -> Set (Set a)
setBigProduct s = case remove s of
  Nothing -> single empty
  Just (xs, xss) -> learnSet xs empty $ do
    let xss' = setBigProduct xss
    x <- xs
    setMap (insert x) xss'

instance Container a (Set a) where s ? e = setPrimElim False (Set.member e) s
instance Iterable a (Set a) where { foldl f i = setPrimElim i $ Set.foldl' f i ; foldr f i = setPrimElim i $ Set.foldr' f i }
instance (Ord a) => Buildable a (Set a) where { nil = empty ; (&) = insert }
instance Eq (Set a) where (==) = setPrimElim2' True (const False) (==)
instance Ord (Set a) where compare = setPrimElim2 EQ (\ s -> compare Set.empty s) (\ s -> compare s Set.empty) compare
instance PartialOrder (Set a) where (⊑) = setPrimElim2 True (const True) (const False) $ Set.isSubsetOf
instance Product Set where xs <*> ys = learnSet xs empty $ learnSet ys empty $ build $ toList xs <*> toList ys
instance Bind Set where aM >>= k = joins $ map k $ toList aM
instance MonadBot Set where mbot = empty
instance MonadPlus Set where (<+>) = union
instance MonadAppend Set where (<++>) = union
instance Bot (Set a) where bot = empty
instance Join (Set a) where (\/) = union
instance Meet (Set a) where (/\) = intersection
instance Monoid (Set a) where { null = empty ; (++) = union }
instance JoinLattice (Set a)

-- }}}

-- ListSet {{{

newtype ListSet a = ListSet { unListSet :: [a] }
  deriving 
    ( Container a, Iterable a, Buildable a
    , Monoid
    , Unit, Functor, Applicative, Product, Bind, Monad
    )
instance (Ord a) => PartialOrder (ListSet a) where pcompare = pcompare `on` toSet
instance Bot (ListSet a) where bot = null
instance Join (ListSet a) where (\/) = (++)
instance MonadBot ListSet where mbot = bot
instance MonadPlus ListSet where (<+>) = (\/)
instance JoinLattice (ListSet a)

-- }}}

-- Map {{{

data Map k v where
  EmptyMap :: Map k v
  Map :: (Ord k) => Map.Map k v -> Map k v
type Old v = v
type New v = v

mapPrimElim :: b -> ((Ord k) => Map.Map k v -> b) -> Map k v -> b
mapPrimElim i f = \case { EmptyMap -> i ; Map p -> f p }

mapPrimElimOn :: Map k v -> b -> ((Ord k) => Map.Map k v -> b) -> b
mapPrimElimOn = rotateR mapPrimElim

mapPrimElim2 :: b 
  -> ((Ord k) => Map.Map k v -> b) 
  -> ((Ord k) => Map.Map k v -> b) 
  -> ((Ord k) => Map.Map k v -> Map.Map k v -> b) 
  -> Map k v -> Map k v -> b
mapPrimElim2 i f1 f2 ff s1 s2 = 
  mapPrimElimOn s1 (mapPrimElimOn s2 i f1) $ \ p1 -> 
    mapPrimElimOn s2 (f2 p1) $ \ p2 -> 
      ff p1 p2

mapPrimElim2' :: b -> ((Ord k) => Map.Map k v -> b) -> ((Ord k) => Map.Map k v -> Map.Map k v -> b) -> Map k v -> Map k v -> b
mapPrimElim2' i f = mapPrimElim2 i f f

toPrimMap    :: Map k v -> Map.Map k v                  ; toPrimMap        = mapPrimElim Map.empty id
learnMap     :: Map k v -> b -> ((Ord k) => b) -> b     ; learnMap m i f   = mapPrimElimOn m i $ const f
mapEmpty     :: Map k v                                 ; mapEmpty         = EmptyMap
mapIsEmpty   :: Map k v -> Bool                         ; mapIsEmpty       = mapPrimElim True Map.null
mapKeys      :: Map k v -> Set k                        ; mapKeys          = mapPrimElim empty $ Set . Map.keysSet
mapInsert    :: (Ord k) => k -> v -> Map k v -> Map k v ; mapInsert        = mapInsertWith $ const id
mapSingleton :: (Ord k) => k -> v -> Map k v            ; mapSingleton k v = mapInsert k v mapEmpty

mapInsertWith :: (Ord k) => (Old v -> New v -> v) -> k -> v -> Map k v -> Map k v
mapInsertWith f k v = mapPrimElim (Map $ Map.singleton k v) $ Map . Map.insertWith (flip f) k v

mapRemove :: Map k v -> Maybe ((k, v), Map k v)
mapRemove = mapPrimElim Nothing $ map (mapSnd Map) . Map.minViewWithKey

mapUnionWith :: (Old v -> New v -> v) -> Map k v -> Map k v -> Map k v
mapUnionWith f = mapPrimElim2' mapEmpty Map $ Map .: Map.unionWith (flip f)

mapIntersectionWith :: (Old v -> New v -> v) -> Map k v -> Map k v -> Map k v
mapIntersectionWith f = mapPrimElim2' mapEmpty (const mapEmpty) $ Map .: Map.intersectionWith (flip f)

mapModify :: (v -> v) -> k -> Map k v -> Map k v
mapModify f k m = learnMap m mapEmpty $ case m # k of
  Nothing -> m
  Just x -> mapInsert k (f x) m

onlyKeys :: (Ord k) => Set k -> Map k v -> Map k v
onlyKeys s m = iterOn s mapEmpty $ \ k -> maybeElim id (mapInsert k) $ m # k

instance Iterable (k, v) (Map k v) where
  foldl f i = mapPrimElim i $ Map.foldlWithKey' (curry . f) i
  foldr f i = mapPrimElim i $ Map.foldrWithKey' (curry f) i
instance (Eq k, Eq v) => Eq (Map k v) where (==) = mapPrimElim2 True (const False) (const False) (==)
instance (Ord k, Ord v) => Ord (Map k v) where compare = mapPrimElim2 EQ (\ m -> compare Map.empty m) (\ m -> compare m Map.empty) compare
instance (Ord k, PartialOrder v) => PartialOrder (Map k v) where (⊑) = mapPrimElim2 True (const True) (const False) $ Map.isSubmapOfBy (⊑)
instance Indexed k v (Map k v) where m # k = mapPrimElim Nothing (Map.lookup k) m
instance (Eq v) => Container (k, v) (Map k v) where m ? (k,v) = maybeElim False (== v) $ m # k
instance (Ord k) => Buildable (k, v) (Map k v) where { nil = mapEmpty ; (&) = uncurry mapInsert }
instance Bot (Map k v) where bot = mapEmpty
instance (Join v) => Join (Map k v) where (\/) = mapUnionWith (\/)
instance (JoinLattice v) => JoinLattice (Map k v)

-- }}}

-- IO {{{

print  :: (MonadIO m) => String -> m () ; print  = liftIO . Prelude.putStrLn . toChars
failIO :: (MonadIO m) => String -> m a  ; failIO = liftIO . Prelude.fail . toChars

instance Unit        IO where unit = Prelude.return
instance Functor     IO where map = mmap
instance Applicative IO where (<@>) = mapply
instance Product     IO where (<*>) = mpair
instance Bind        IO where (>>=) = (Prelude.>>=)
instance MonadIO     IO where liftIO = id
instance Monad       IO

-- }}}

-- Q {{{

instance Unit        Q where unit = Prelude.return
instance Functor     Q where map = mmap
instance Applicative Q where (<@>) = mapply
instance Product     Q where (<*>) = mpair
instance Bind        Q where (>>=) = (Prelude.>>=)
instance MonadQ      Q where liftQ = id
instance MonadBot    Q where mbot = Prelude.fail $ toChars "mbot"
instance Monad       Q

-- }}}

-- Fix {{{

data Stamped a f = Stamped { stampedID :: a , stamped :: f }
instance (Eq a) => Eq (Stamped a f) where (==) = (==) `on` stampedID
instance (Ord a) => Ord (Stamped a f) where compare = compare `on` stampedID

newtype Fix f = Fix { unFix :: f (Fix f) }
instance (Functorial Eq f) => Eq (Fix f) where
  Fix x == Fix y = with (functorial :: W (Eq (f (Fix f)))) $ x == y
instance (Functorial Eq f, Functorial Ord f) => Ord (Fix f) where
  Fix x `compare` Fix y = with (functorial :: W (Ord (f (Fix f)))) $ x `compare` y

data StampedFix a f = StampedFix { stampedFixID :: a , stampedFix :: f (StampedFix a f) } 
stripStampedFix :: (Functor f) => StampedFix a f -> Fix f
stripStampedFix (StampedFix _ f) = Fix $ map stripStampedFix f
instance (Eq a)           => Eq (StampedFix a f)           where (==)     = (==)     `on` stampedFixID
instance (Ord a)          => Ord (StampedFix a f)          where compare  = compare  `on` stampedFixID
instance (PartialOrder a) => PartialOrder (StampedFix a f) where pcompare = pcompare `on` stampedFixID

-- }}}

-- Annotated {{{

data Annotated ann a = Annotated { annotation :: ann , annValue :: a }

-- }}}
