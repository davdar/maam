module Lang.Hask.Syntax 
  ( module Lang.Hask.Syntax
  , module CoreSyn
  , module Literal
  , module Name
  ) where

import FP

import CoreSyn
import Var
import Literal
import Name
import UniqSupply

data Pico =
    VarP Name
  | LitP Literal

data PreAtom e =
    PicoA Pico
  | LamA Name Name e
type Atom = PreAtom Call

data PreCall e =
    LetC Name (PreAtom e) e
  | LetrecC [(Name, PreAtom e)] e
  | AppfC Pico Pico Pico
  | AppkC Pico Pico
  | CaseC Pico [(AltCon, [Name], e)]
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
letAtom = undefined

reify :: (CPSM m) => CPSKon Call m Pico -> m Pico
reify = undefined

reflect :: (CPSM m) => Pico -> CPSKon Call m Pico
reflect = undefined

cpsAtom :: (CPSM m) => Expr Var -> m Atom
cpsAtom = undefined

cpsM :: (CPSM m) => Expr Var -> m Pico
cpsM e = case e of
  Var xv -> return $ VarP $ Var.varName xv
  Lit l -> return $ LitP l
  App e₁ e₂ ->
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      p₁ <- cpsM e₁
      p₂ <- cpsM e₂
      k <- reify ko
      return $ Fix $ AppfC p₁ p₂ k
  Lam xv e' -> do
    let x = Var.varName xv
    k <- fresh "k"
    c <- withOpaqueC (reflect $ VarP k) $ cpsM e'
    f <- fresh "f"
    letAtom f $ LamA x k c
  Let (NonRec xv e₁) e₂ -> do
    let x = Var.varName xv
    a <- cpsAtom e₁
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      c <- withOpaqueC ko $ cpsM e₂
      return $ Fix $ LetC x a c
  Let (Rec xves) e₂ -> do
    xas <- mapOnM xves $ uncurry $ \ xv e' -> do
      let x = Var.varName xv
      a <- cpsAtom e'
      return (x, a)
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      c <- withOpaqueC ko $ cpsM e₂
      return $ Fix $ LetrecC xas c
  Case e' xv _ bs -> do
    a <- cpsAtom e'
    p <- letAtom (Var.varName xv) a
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      b's <- mapOnM bs $ \ (con, xvs, e'') -> do
        let xs = map Var.varName xvs
        c <- withOpaqueC ko $ cpsM e''
        return (con, xs, c)
      return $ Fix $ CaseC p b's
  Cast e' _ -> cpsM e'
  Tick _ e'    -> cpsM e'
  Type _   -> error "type in term"
  Coercion _ -> error "coercion in term"
