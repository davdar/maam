module Lang.Hask.CPS where

import FP

import qualified CoreSyn as H
import Var
import Literal
import Name
import UniqSupply

makePrisms ''H.AltCon

data Pico =
    Var Name
  | Lit Literal
  deriving (Eq, Ord)

data PreAtom e =
    Pico Pico
  | LamF Name Name e
  | LamK Name e
  | Thunk Name Name Name Pico Pico
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
  | Rec [(Name, Name, Name)] e
  | Letrec [(Name, PreAtom e)] e
  | AppK Pico Pico
  | AppF Pico Pico Pico
  | Case Pico [PreCaseBranch e]
  | Halt Pico
  deriving (Eq, Ord)
instance (Functorial Eq PreCall) where functorial = W
instance (Functorial Ord PreCall) where functorial = W
type Call = Fix PreCall

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
type CPSM m = (Monad m, MonadCont Call m, MonadOpaqueCont CPSKon Call m, MonadState UniqSupply m)

fresh :: (CPSM m) => String -> m Name
fresh x = do
  supply <- get
  let (u, supply') = takeUniqFromSupply supply
  put supply'
  return $ mkSystemName u $ mkVarOcc $ toChars x

atom :: (CPSM m) => Atom -> m Pico
atom a = do
  x <- fresh "x"
  letAtom x a
  return $ Var x

letAtom :: (CPSM m) => Name -> Atom -> m ()
letAtom x a = modifyC (return . Fix . Let x a) $ return ()

rec :: (CPSM m) => [Name] -> m ()
rec xs = do
  rxrxs <- mapOnM xs $ \ x -> do
    r <- fresh "r"
    xr <- fresh "xr"
    return (r, xr, x)
  modifyC (return . Fix . Rec rxrxs) $ return ()

reify :: (CPSM m) => CPSKon Call m Pico -> m Pico
reify (MetaKon mk) = do
  x <- fresh "x"
  c <- mk $ Var x
  atom $ LamK x c
reify (ObjectKon k _) = return k

reflect :: (CPSM m) => Pico -> CPSKon Call m Pico
reflect k = ObjectKon k $ \ x -> do
  return $ Fix $ AppK k x

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
    xr <- fresh "xr"
    k <- fresh "k"
    atom $ Thunk r xr k p₁ p₂
  H.Lam xv e' -> do
    let x = Var.varName xv
    k <- fresh "k"
    c <- opaqueWithC (reflect $ Var k) $ cpsM e'
    atom $ LamF x k c
  H.Let (H.NonRec xv e₁) e₂ -> opaqueCallCC $ \ (ko :: CPSKon Call m Pico) -> do
    let x = Var.varName xv
    a <- cpsAtom e₁
    c <- opaqueWithC ko $ cpsM e₂
    return $ Fix $ Let x a c
  H.Let (H.Rec xves) e₂ -> opaqueCallCC $ \ (ko :: CPSKon Call m Pico) -> do
    rec $ map (Var.varName . fst) xves
    xas <- mapOnM xves $ uncurry $ \ xv e' -> do
      let x = Var.varName xv
      a <- cpsAtom e'
      return (x, a)
    c <- opaqueWithC ko $ cpsM e₂
    return $ Fix $ Letrec xas c
  H.Case e' xv _ bs -> opaqueCallCC $ \ (ko :: CPSKon Call m Pico) -> do
    let x = Var.varName xv
    a <- cpsAtom e'
    letAtom x a
    -- the reverse here is to move DEFAULT branch (if it occurs) to the end,
    -- since it always shows up at the beginning as per ghc spec.
    b's <- mapOnM (reverse bs) $ \ (con, xvs, e'') -> do
      let xs = map Var.varName xvs
      c <- opaqueWithC ko $ cpsM e''
      return $ CaseBranch con xs c
    return $ Fix $ Case (Var x) b's
  H.Cast e' _ -> cpsM e'
  H.Tick _ e' -> cpsM e'
  H.Type _ -> error "type in term"
  H.Coercion _ -> error "coercion in term"
