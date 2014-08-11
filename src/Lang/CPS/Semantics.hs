module Lang.CPS.Semantics where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

type MonadCPS δ μ m = 
  ( MonadFail m
  , MonadZero m
  , MonadPlus m
  , MonadState (Env μ) m
  , MonadState (Store δ μ) m
  , MonadState (Time μ (Σ δ μ)) m
  , MonadStep m
  , Ord (Addr μ)
  , Ord (Val δ μ)
  )

type Analysis δ μ m =
  ( AAM μ
  , Delta δ
  , Δ δ μ
  , MonadCPS δ μ m
  , PartialOrder (SS m Call)
  , JoinLattice (SS m Call)
  , JoinLattice (Val δ μ)
  )

new :: (Analysis δ μ m) => P δ -> P μ -> Name -> m (Addr μ)
new δ μ x = alloc μ x <$> getP $ timeP μ $ σ δ μ

var :: (MonadCPS δ μ m) => P δ -> P μ -> Name -> m (Val δ μ)
var δ μ x = do
  e <- getL $ envL μ
  s <- getL $ storeL δ μ
  useMaybeZero $ index s *$ index e $ x

bind :: (Analysis δ μ m) => P δ -> P μ -> Name -> Val δ μ -> m ()
bind δ μ x vD = do
  l <- new δ μ x
  modifyL (envL μ) $ pinsert x l
  modifyL (storeL δ μ) $ pinsertWith (\/) l vD

atom :: (Analysis δ μ m) => P δ -> P μ -> Atom -> m (Val δ μ)
atom δ _ (LitA l) = return $ lit δ l
atom δ μ (Var x) = var δ μ x
atom δ μ (Prim o a) = do
  op δ o <$> atom δ μ a
atom δ μ (Lam xs c) = clo δ . Clo xs c <$> getP $ envP μ

elimBoolM :: (Analysis δ μ m) => P δ -> Val δ μ -> m Bool
elimBoolM = msum .: elimBool

elimCloM :: (Analysis δ μ m) => P δ -> Val δ μ -> m (Clo μ)
elimCloM = msum .: elimClo

tickM :: (Analysis δ μ m) => P δ -> P μ -> Call -> m ()
tickM δ μ c = do
  e <- getP $ envP μ
  s <- getP $ storeP δ μ
  modifyP (timeP μ $ σ δ μ) $ tick μ (c, e, s)

call :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> m Call
call δ μ _ (If a tc fc) = do
  b <- elimBoolM δ *$ atom δ μ a
  return $ if b then tc else fc
call δ μ _ (App fa (aes :: [Atom])) = do
  Clo xs c e <- elimCloM δ *$ atom δ μ fa
  vs <- atom δ μ <*$> aes
  xvs <- useMaybeZero $ zipSameLength xs vs
  putP (envP μ) e
  traverseOn xvs $ uncurry $ bind δ μ
  tickM δ μ c
  return c
call _ _ _ (Halt a) = return $ Halt a

exec :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> SS m Call
exec δ μ m c = poiter (mstep $ call δ μ m) $ unit c

collectExec :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> SS m Call
collectExec δ μ m c = collect (mstep $ call δ μ m) $ unit c
