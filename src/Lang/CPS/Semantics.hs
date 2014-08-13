module Lang.CPS.Semantics where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

data Ψ δ μ = Ψ 
  { ψcall :: Call
  -- , ψenv :: Env μ (Ψ δ μ)
  -- , ψstore :: Store δ μ (Ψ δ μ)
  }

ψ :: P δ -> P μ -> P (Ψ δ μ)
ψ P P = P

type MonadCPS δ μ m = 
  ( MonadFail m
  , MonadZero m
  , MonadPlus m
  , MonadState (Env μ (Ψ δ μ)) m
  , MonadState (Store δ μ (Ψ δ μ)) m
  , MonadState (LexicalTime μ (Ψ δ μ)) m
  , MonadState (DynamicTime μ (Ψ δ μ)) m
  , MonadStep m
  , Ord (LexicalTime μ (Ψ δ μ))
  , Ord (DynamicTime μ (Ψ δ μ))
  , Ord (Val δ μ (Ψ δ μ))
  )

type Analysis δ μ m =
  ( AAM μ
  , Delta δ
  , Δ δ μ
  , MonadCPS δ μ m
  , PartialOrder (SS m Call)
  , JoinLattice (SS m Call)
  , JoinLattice (Val δ μ (Ψ δ μ))
  )

new :: (Analysis δ μ m) => P δ -> P μ -> Name -> m (Addr μ (Ψ δ μ))
new δ μ x = do
  lτ <- getP $ lexicalTimeP μ $ ψ δ μ
  dτ <- getP $ dynamicTimeP μ $ ψ δ μ
  return $ Addr x lτ dτ

bind :: (Analysis δ μ m) => P δ -> P μ -> Name -> Val δ μ (Ψ δ μ) -> m ()
bind δ μ x vD = do
  l <- new δ μ x
  modifyL (envL μ $ ψ δ μ) $ pinsert x l
  modifyL (storeL δ μ $ ψ δ μ) $ pinsertWith (\/) l vD

var :: (Analysis δ μ m) => P δ -> P μ -> Name -> m (Val δ μ (Ψ δ μ))
var δ μ x = do
  e <- getL $ envL μ $ ψ δ μ
  s <- getL $ storeL δ μ $ ψ δ μ
  useMaybeZero $ index s *$ index e $ x

atom :: (Analysis δ μ m) => P δ -> P μ -> Atom -> m (Val δ μ (Ψ δ μ))
atom δ _ (LitA l) = return $ lit δ l
atom δ μ (Var x) = var δ μ x
atom δ μ (Prim o a) = do
  op δ o <$> atom δ μ a
atom δ μ (Lam xs c) = do
  e <- getP $ envP μ $ ψ δ μ
  lτ <- getP $ lexicalTimeP μ $ ψ δ μ
  return $ clo δ $ Clo xs c e lτ

elimBoolM :: (Analysis δ μ m) => P δ -> Val δ μ (Ψ δ μ) -> m Bool
elimBoolM = msum .: elimBool

elimCloM :: (Analysis δ μ m) => P δ -> Val δ μ (Ψ δ μ) -> m (Clo μ (Ψ δ μ))
elimCloM = msum .: elimClo

tickM :: (Analysis δ μ m) => P δ -> P μ -> Call -> m ()
tickM δ μ c = do
  _ <- getP $ envP μ $ ψ δ μ
  _ <- getP $ storeP δ μ $ ψ δ μ
  modifyP (dynamicTimeP μ $ ψ δ μ) $ tick $ Ψ c -- e s
  modifyP (lexicalTimeP μ $ ψ δ μ) $ tick $ Ψ c -- e s

call :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> m Call
call δ μ _ (If a tc fc) = do
  b <- elimBoolM δ *$ atom δ μ a
  return $ if b then tc else fc
call δ μ m (App fa aes) = do
  Clo xs c e lτ <- elimCloM δ *$ atom δ μ fa
  vs <- atom δ μ <*$> aes
  xvs <- useMaybeZero $ zipSameLength xs vs
  putP (envP μ $ ψ δ μ) e
  putP (lexicalTimeP μ $ ψ δ μ) lτ
  traverseOn xvs $ uncurry $ bind δ μ
  tickM δ μ c
  gc δ μ m c
  return c
call _ _ _ (Halt a) = return $ Halt a

-- 'Standard' semantics --
exec :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> SS m Call
exec δ μ m c = poiter (mstep $ call δ μ m) $ unit c

-- Collecting semantics --
collectExec :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> SS m Call
collectExec δ μ m c = collect (mstep $ call δ μ m) $ unit c

--------
-- GC --
--------

freeVarsLam :: (Analysis δ μ m) => P δ -> P μ -> P m -> [Name] -> Call -> Set Name
freeVarsLam δ μ m xs c = freeVarsCall δ μ m c \-\ sset xs

freeVarsAtom :: (Analysis δ μ m) => P δ -> P μ -> P m -> Atom -> Set Name
freeVarsAtom _ _ _ (LitA _) = bot
freeVarsAtom _ _ _ (Var x) = ssingleton x
freeVarsAtom δ μ m (Prim _ a) = freeVarsAtom δ μ m a
freeVarsAtom δ μ m (Lam xs c) = freeVarsLam δ μ m xs c

freeVarsCall :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> Set Name
freeVarsCall δ μ m (If a tc fc) = freeVarsAtom δ μ m a \/ freeVarsCall δ μ m tc \/ freeVarsCall δ μ m fc
freeVarsCall δ μ m (App fa aes) = freeVarsAtom δ μ m fa \/ joins (map (freeVarsAtom δ μ m) aes)
freeVarsCall δ μ m (Halt a) = freeVarsAtom δ μ m a

callTouched :: (Analysis δ μ m) => P δ -> P μ -> P m -> Env μ (Ψ δ μ) -> Call -> Set (Addr μ (Ψ δ μ))
callTouched δ μ m e c = closureTouched δ μ m e [] c

closureTouched :: (Analysis δ μ m) => P δ -> P μ -> P m -> Env μ (Ψ δ μ) -> [Name] -> Call -> Set (Addr μ (Ψ δ μ))
closureTouched δ μ m e xs c = useMaybeSet . index (runEnv e) *$~ freeVarsLam δ μ m xs c

addrTouched :: (Analysis δ μ m) => P δ -> P μ -> P m -> Store δ μ (Ψ δ μ) -> Addr μ (Ψ δ μ) -> Set (Addr μ (Ψ δ μ))
addrTouched δ μ m s l = 
  let clos = elimClo δ *$~ useMaybeSet . index (runStore s) $ l
  in clos >>=~ \ (Clo xs c e _) -> closureTouched δ μ m e xs c

gc :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> m ()
gc δ μ m c = do
  e <- getP $ envP μ $ ψ δ μ
  s <- getP $ storeP δ μ $ ψ δ μ
  let live = collect (cextend $ addrTouched δ μ m s) $ callTouched δ μ m e c
  modifyL (storeL δ μ (ψ δ μ)) $ ponlyKeys live
  return ()

callGC :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> m Call
callGC δ μ m c = do
  c' <- call δ μ m c
  gc δ μ m c'
  return c'

collectExecGC :: (Analysis δ μ m) => P δ -> P μ -> P m -> Call -> SS m Call
collectExecGC δ μ m c = collect (mstep $ callGC δ μ m) $ unit c
