module Lang.Hask.CPS where

import FP

import qualified CoreSyn as H
import Var
import Literal
import Name
import UniqSupply
import Lang.Hask.Compat ()

data Pico =
    Var Name
  | Lit Literal
  | Type
  deriving (Eq, Ord)

data PreAtom e =
    Pico Pico
  | LamF Name Name e
  | LamK Name e
  | Thunk Name Int Name Name Pico Pico
  deriving (Eq, Ord)
type Atom = PreAtom Call

data PreCaseBranch e = CaseBranch
  { caseBranchCon :: H.AltCon
  , caseBranchArgs :: [Name]
  , caseBranchCall :: e
  } deriving (Eq, Ord)
type CaseBranch = PreCaseBranch Call

data PreCall e =
    Let Name (PreAtom e) e
  | Rec [(Name, Name)] e
  | Letrec [(Name, PreAtom e)] e
  | AppK Pico Pico
  | AppF Int Name Pico Pico Pico
  | Case Int Name Pico [PreCaseBranch e]
  | Halt Pico
  deriving (Eq, Ord)
instance (Functorial Eq PreCall) where functorial = W
instance (Functorial Ord PreCall) where functorial = W
type Call = StampedFix Int PreCall
-- CPS Conversion

data CPSKon r m a where
  MetaKon :: (a -> m r) -> CPSKon r m a
  ObjectKon :: Pico -> (Pico -> m Call) -> CPSKon Call m Pico
instance Morphism3 (ContFun r) (CPSKon r) where
  morph3 (ContFun mk) = MetaKon mk
instance Morphism3 (CPSKon r) (ContFun r) where
  morph3 :: CPSKon r ~~> ContFun r
  morph3 (MetaKon mk) = ContFun mk
  morph3 (ObjectKon _ mk) = ContFun mk
instance Isomorphism3 (ContFun r) (CPSKon r) where
instance Balloon CPSKon Call where
  inflate :: (Monad m) => CPSKon Call m ~> CPSKon Call (OpaqueContT CPSKon Call m)
  inflate (MetaKon (mk :: a -> m Call)) = MetaKon $ \ (a :: a) -> makeMetaKonT $ \ (k :: Call -> m Call) -> k *$ mk a
  inflate (ObjectKon pk (mk :: Pico -> m Call)) = ObjectKon pk $ \ p -> makeMetaKonT $ \ (k :: Call -> m Call) -> k *$ mk p
  deflate :: (Monad m) => CPSKon Call (OpaqueContT CPSKon Call m) ~> CPSKon Call m
  deflate (MetaKon (mk :: a -> OpaqueContT CPSKon Call m Call)) = MetaKon $ \ (a :: a) -> runMetaKonTWith return $ mk a
  deflate (ObjectKon pk (mk :: Pico -> OpaqueContT CPSKon Call m Call)) = ObjectKon pk $ \ p -> evalOpaqueKonT $ mk p

data CPS𝒮 = CPS𝒮
  { cps𝒮UniqSupply :: UniqSupply
  , cps𝒮ProgLoc    :: Int
  }
makeLenses ''CPS𝒮

type CPSM m = (Monad m, MonadCont Call m, MonadOpaqueCont CPSKon Call m, MonadState CPS𝒮 m)

fresh :: (CPSM m) => String -> m Name
fresh x = do
  supply <- getL cps𝒮UniqSupplyL
  let (u, supply') = takeUniqFromSupply supply
  putL cps𝒮UniqSupplyL supply'
  return $ mkSystemName u $ mkVarOcc $ toChars x

stamp :: (Monad m, MonadState CPS𝒮 m) => PreCall Call -> m Call
stamp c = do
  i <- nextL cps𝒮ProgLocL
  return $ StampedFix i c

atom :: (CPSM m) => Atom -> m Pico
atom a = do
  x <- fresh "x"
  letAtom x a
  return $ Var x

letAtom :: (CPSM m) => Name -> Atom -> m ()
letAtom x a = do
  i <- nextL cps𝒮ProgLocL
  modifyC (return . StampedFix i . Let x a) $ return ()

rec :: (CPSM m) => [Name] -> m ()
rec xs = do
  rxs <- mapOnM xs $ \ x -> do
    r <- fresh "r"
    return (r, x)
  i <- nextL cps𝒮ProgLocL
  modifyC (return . StampedFix i . Rec rxs) $ return ()

letrec :: (CPSM m) => [(Name, Atom)] -> m ()
letrec xas = do
  i <- nextL cps𝒮ProgLocL
  modifyC (return . StampedFix i . Letrec xas) $ return ()

reify :: (CPSM m) => CPSKon Call m Pico -> m Pico
reify (MetaKon mk) = do
  x <- fresh "x"
  c <- mk $ Var x
  atom $ LamK x c
reify (ObjectKon k _) = return k

reflect :: (CPSM m) => Pico -> CPSKon Call m Pico
reflect k = ObjectKon k $ \ x -> do
  stamp $ AppK k x

cpsAtom :: (CPSM m) => H.Expr Var -> m Atom
cpsAtom e = case e of
  H.Lam xv e' -> do
    let x = Var.varName xv
    k <- fresh "k"
    c <- opaqueWithC (reflect $ Var k) $ cpsM e'
    return $ LamF x k c
  _ -> do
    p <- cpsM e
    return $ Pico p

cpsM :: (CPSM m) => H.Expr Var -> m Pico
cpsM e = case e of
  H.Var xv -> return $ Var $ Var.varName xv
  H.Lit l -> return $ Lit l
  H.App e₁ e₂ -> do
    p₁ <- cpsM e₁
    p₂ <- cpsM e₂
    r <- fresh "r"
    xi <- nextL cps𝒮ProgLocL
    x <- fresh "x"
    k <- fresh "k"
    atom $ Thunk r xi x k p₁ p₂
  H.Lam xv e' -> do
    let x = Var.varName xv
    k <- fresh "k"
    c <- opaqueWithC (reflect $ Var k) $ cpsM e'
    atom $ LamF x k c
  H.Let (H.NonRec xv e₁) e₂ -> do
    let x = Var.varName xv
    a <- cpsAtom e₁
    letAtom x a
    cpsM e₂
  H.Let (H.Rec xves) e₂ -> do
    rec $ map (Var.varName . fst) xves
    xas <- mapOnM xves $ uncurry $ \ xv e' -> do
      let x = Var.varName xv
      a <- cpsAtom e'
      return (x, a)
    letrec xas
    cpsM e₂
  H.Case e' xv _ bs -> opaqueCallCC $ \ (ko :: CPSKon Call m Pico) -> do
    ko' <- reflect ^$ reify ko
    let x = Var.varName xv
    a <- cpsAtom e'
    letAtom x a
    -- the reverse here is to move DEFAULT branch (if it occurs) to the end,
    -- since it always shows up at the beginning as per ghc spec.
    b's <- mapOnM (reverse bs) $ \ (con, xvs, e'') -> do
      let xs = map Var.varName xvs
      c <- opaqueWithC ko' $ cpsM e''
      return $ CaseBranch con xs c
    xi' <- nextL cps𝒮ProgLocL
    x' <- fresh "x"
    stamp $ Case xi' x' (Var x) b's
  H.Cast e' _ -> cpsM e'
  H.Tick _ e' -> cpsM e'
  H.Type _ -> return Type
  H.Coercion _ -> error "coercion in term"

cps :: (Monad m, MonadReader UniqSupply m) =>  H.Expr Var -> m Call
cps c = do
  uniqueSupply <- ask
  return $ evalState (CPS𝒮 uniqueSupply $ toi 0) $ runMetaKonT (cpsM c) $ stamp . Halt
