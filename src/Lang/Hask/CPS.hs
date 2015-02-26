module Lang.Hask.CPS where

import FP

import qualified CoreSyn as H
import Var
import Literal
import Name
import UniqSupply

data Pico =
    Var Name
  | Lit Literal

data PreAtom e =
    Pico Pico
  | LamF Name Name e
  | LamK Name e
type Atom = PreAtom Call

data PreCall e =
    Let Name (PreAtom e) e
  | Rec [Name] e
  | Letrec [(Name, PreAtom e)] e
  | AppF Pico Pico Pico
  | AppK Pico Pico
  | Case Pico [(H.AltCon, [Name], e)]
type Call = Fix PreCall

-- CPS Conversion

data CPSKon r m a where
  MetaKon :: (a -> m r) -> CPSKon r m a
  ObjectKon :: Pico -> (Pico -> m Call) -> CPSKon Call m Pico
instance Morphism3 (KFun r) (CPSKon r) where
  morph3 (KFun mk) = MetaKon mk
instance Morphism3 (CPSKon r) (KFun r) where
  morph3 :: CPSKon r ~~> KFun r
  morph3 (MetaKon mk) = KFun mk
  morph3 (ObjectKon _ mk) = KFun mk
instance Isomorphism3 (KFun r) (CPSKon r) where
instance Balloon CPSKon Call where
  inflate :: (Monad m) => CPSKon Call m ~> CPSKon Call (OpaqueKonT CPSKon Call m)
  inflate (MetaKon mk) = MetaKon $ \ a -> makeMetaKonT $ \ k -> k *$ mk a
  inflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> makeMetaKonT $ \ k -> k *$ mk ax
  deflate :: (Monad m) => CPSKon Call (OpaqueKonT CPSKon Call m) ~> CPSKon Call m
  deflate (MetaKon mk) = MetaKon $ \ a -> runMetaKonTWith return $ mk a
  deflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> evalOpaqueKonT $ mk ax
type CPSM m = (MonadOpaqueKon CPSKon Call m, MonadState UniqSupply m)

fresh :: (CPSM m) => String -> m Name
fresh x = do
  supply <- get
  let (u, supply') = takeUniqFromSupply supply
  put supply'
  return $ mkSystemName u $ mkVarOcc $ toChars x

letAtom :: (CPSM m) => Name -> Atom -> m Pico
letAtom x a = do
  modifyC (return . Fix . Let x a) $ 
    return $ Var x

reify :: (CPSM m) => CPSKon Call m Pico -> m Pico
reify (MetaKon mk) = do
  x <- fresh "x"
  c <- mk $ Var x
  k <- fresh "k"
  letAtom k $ LamK x c
reify (ObjectKon k _) = return k

reflect :: (CPSM m) => Pico -> CPSKon Call m Pico
reflect k = ObjectKon k $ \ x -> do
  return $ Fix $ AppK k x

cpsAtom :: (CPSM m) => H.Expr Var -> m Atom
cpsAtom e = case e of
  H.Lam xv e' -> do
    let x = Var.varName xv
    k <- fresh "k"
    c <- withOpaqueC (reflect $ Var k) $ cpsM e'
    return $ LamF x k c
  _ -> do
    p <- cpsM e
    return $ Pico p

cpsM :: (CPSM m) => H.Expr Var -> m Pico
cpsM e = case e of
  H.Var xv -> return $ Var $ Var.varName xv
  H.Lit l -> return $ Lit l
  H.App e₁ e₂ ->
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      p₁ <- cpsM e₁
      p₂ <- cpsM e₂
      k <- reify ko
      return $ Fix $ AppF p₁ p₂ k
  H.Lam xv e' -> do
    let x = Var.varName xv
    k <- fresh "k"
    c <- withOpaqueC (reflect $ Var k) $ cpsM e'
    f <- fresh "f"
    letAtom f $ LamF x k c
  H.Let (H.NonRec xv e₁) e₂ -> do
    let x = Var.varName xv
    a <- cpsAtom e₁
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      c <- withOpaqueC ko $ cpsM e₂
      return $ Fix $ Let x a c
  H.Let (H.Rec xves) e₂ -> do
    modifyC (return . Fix . Rec (map (Var.varName . fst) xves)) $ do
      xas <- mapOnM xves $ uncurry $ \ xv e' -> do
        let x = Var.varName xv
        a <- cpsAtom e'
        return (x, a)
      callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
        c <- withOpaqueC ko $ cpsM e₂
        return $ Fix $ Letrec xas c
  H.Case e' xv _ bs -> do
    a <- cpsAtom e'
    p <- letAtom (Var.varName xv) a
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      b's <- mapOnM bs $ \ (con, xvs, e'') -> do
        let xs = map Var.varName xvs
        c <- withOpaqueC ko $ cpsM e''
        return (con, xs, c)
      return $ Fix $ Case p b's
  H.Cast e' _ -> cpsM e'
  H.Tick _ e' -> cpsM e'
  H.Type _ -> error "type in term"
  H.Coercion _ -> error "coercion in term"
