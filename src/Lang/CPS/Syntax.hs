module Lang.CPS.Syntax where

import FP

type Name = String
newtype SName = SName { runSName :: Name }
  deriving (Eq, Ord)
data RName = RName
  { rNameID :: Int
  , rName :: SName
  }
instance Eq RName where
  (==) = (==) `on` rNameID
instance Ord RName where
  compare = compare `on` rNameID

data Lit = I Int | B Bool
  deriving (Eq, Ord)
coerceI :: Lit -> Maybe Int
coerceI (I i) = Just i
coerceI _ = Nothing
coerceB :: Lit -> Maybe Bool
coerceB (B b) = Just b
coerceB _ = Nothing

instance PartialOrder Lit where pcompare = discreteOrder
data Op = Add1 | Sub1 | IsNonNeg
  deriving (Eq, Ord)
instance PartialOrder Op where pcompare = discreteOrder
type SAtom = Atom SName SCall
type RAtom = Atom RName RCall
data Atom n c =
    LitA Lit
  | Var n
  | Prim Op (Atom n c)
  | Lam [n] c
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (Atom n c) where pcompare = discreteOrder
type SCall = Fix (Call SName)
data RCall = RCall 
  { rCallID :: Int
  , rCall :: Call RName RCall
  }
instance Eq RCall where
  (==) = (==) `on` rCallID
instance Ord RCall where
  compare = compare `on` rCallID
data Call n c =
    If (Atom n c) c c 
  | App (Atom n c) [Atom n c]
  | Halt (Atom n c)

-- Unique Naming {{{

type U = ReaderT (Map SName Int) (State (Int, Int))

ubdrL :: Lens (Int, Int) Int
ubdrL = fstL

ulocL :: Lens (Int, Int) Int
ulocL = sndL

uenvP :: P (Map SName Int)
uenvP = P

nextLoc :: U Int
nextLoc = do
  i <- getL ulocL
  putL ulocL $ i + 1
  return i

nextBdr :: U Int
nextBdr = do
  i <- getL ubdrL
  putL ubdrL $ i + 1
  return i

uaskBdr :: SName -> U RName
uaskBdr s = do
  -- if it's not in the map, just choose something fresh...
  i <- maybe return nextBdr . lookup s *$ askP uenvP
  return $ RName i s

freshBdr :: SName -> U (U a -> U a)
freshBdr s = do
  i <- nextBdr
  return $ localP uenvP $ pinsert s i
  
uatom :: SAtom -> U RAtom
uatom (LitA l) = unit $ LitA l
uatom (Var n) = Var <$> uaskBdr n
uatom (Prim o a) = Prim o <$> uatom a
uatom (Lam xs c) = do
  bound <- map composeEndo $ mapM freshBdr xs
  bound $ unit Lam <@> mapM uaskBdr xs <@> ucall c

ucall :: SCall -> U RCall
ucall sc = unit RCall <@> nextLoc <@> case runFix sc of
  If a tc fc -> unit If <@> uatom a <@> ucall tc <@> ucall fc
  App a aes -> unit App <@> uatom a <@> mapM uatom aes
  Halt a -> unit Halt <@> uatom a

sr :: SCall -> RCall
sr = evalState (0, 0) . runReaderT pempty . ucall

-- }}}

-- Smart Constructors {{{

letAtom :: String -> SAtom -> SCall -> SCall
letAtom x a c = Fix $ App (Lam [SName x] c) [a]

letApp :: String -> SAtom -> SAtom -> SCall -> SCall
letApp x f a c = Fix $ App f [a, Lam [SName x] c]

lam :: String -> String -> SCall -> SAtom
lam x k c = Lam [SName x, SName k] c

(@#) :: SAtom -> SAtom -> SCall
k @# x = Fix $ App k [x]

(@@#) :: SAtom -> [SAtom] -> SCall
(@@#) = Fix .: App

v :: String -> SAtom
v = Var . SName

true :: SAtom
true = LitA $ B True

false :: SAtom
false = LitA $ B False

int :: Int -> SAtom
int = LitA . I

halt :: SAtom -> SCall
halt = Fix . Halt

ifc :: SAtom -> SCall -> SCall -> SCall
ifc = Fix ..: If

-- }}}
