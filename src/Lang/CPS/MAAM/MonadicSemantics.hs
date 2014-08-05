module Lang.CPS.MAAM.MonadicSemantics where

import FP
import MAAM

import Lang.CPS.Delta
import Lang.CPS.Syntax

type MonadCPS δ μ m = 
  ( MonadZero m
  , MonadPlus m
  , MonadState (Env μ) m
  , MonadState (Store δ μ) m
  , MonadState (Time μ Call) m
  , MonadMaybeE m
  , MonadStep m
  , Ord (Addr μ)
  , Ord (Val δ μ)
  )

type Analysis δ μ m =
  ( Delta δ
  , AAM μ
  , MonadCPS δ μ m
  , PartialOrder (SS m Call)
  , JoinLattice (SS m Call)
  )

σ :: P Call
σ = callP

new :: (Analysis δ μ m) => P δ -> P μ -> Name -> m (Addr μ)
new _ μ x = alloc μ x <$> getP $ time μ σ

var :: (MonadCPS δ μ m) => P δ -> P μ -> Name -> m (Set (Val δ μ))
var δ μ x = do
  e <- getL $ envL μ
  s <- getL $ storeL δ μ
  useMaybe $ index s *$ index e $ x

bind :: (Analysis δ μ m) => P δ -> P μ -> Name -> Set (Val δ μ) -> m ()
bind δ μ x vD = do
  l <- new δ μ x
  modifyL (envL μ) $ pinsert x l
  modifyL (storeL δ μ) $ pinsertWith (\/) l vD

atomic :: (Analysis δ μ m) => P δ -> P μ -> Atom -> m (Set (Val δ μ))
atomic δ _   (LitA l) = return $ ssingleton $ lit δ l
atomic δ μ (Var x) = var δ μ x
atomic δ μ (Prim o a) = do
  vD <- atomic δ μ a
  return $ op δ o *$~ vD
atomic δ μ (Lam xs c) = mmap (ssingleton . clo δ xs c) $ getP $ envP μ

atomicM :: (Analysis δ μ m) => P δ -> P μ -> Atom -> m (Val δ μ)
atomicM δ μ a = msum *$ atomic δ μ a

elimBoolM :: (Delta δ, MonadCPS δ μ m) => P δ -> Val δ μ -> m Bool
elimBoolM = msum .: elimBool

elimCloM :: (Delta δ, MonadCPS δ μ m) => P δ -> Val δ μ -> m ([Name], Call, Env μ)
elimCloM = msum .: elimClo

call :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> m Call
call δ μ _ (If a tc fc) = do
  b <- elimBoolM δ *$ atomicM δ μ a
  return $ if b then tc else fc
call δ μ _ (App fa (aes :: [Atom])) = do
  (xs, c, e) <- elimCloM δ *$ atomicM δ μ fa
  vs <- mapM (atomic δ μ) aes
  xvs <- useMaybe $ zipSameLength xs vs
  putP (envP μ) e
  traverseOn xvs $ uncurry $ bind δ μ
  return c
call _ _ _ (Halt a) = return $ Halt a

exec :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> SS m Call
exec δ μ m c = poiter (mstep $ call δ μ m) $ unit c

collectExec :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> SS m Call
collectExec δ μ m c = collect (mstep $ call δ μ m) $ unit c
