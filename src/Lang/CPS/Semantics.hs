module Lang.CPS.Semantics where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.CPS.Classes.Delta

type MonadCPS (δ :: *) μ m = 
  ( MonadFail (m δ μ)
  , MonadZero (m δ μ)
  , MonadPlus (m δ μ)
  , MonadStateE (Env μ) (m δ μ)
  , MonadStateE (Store δ μ) (m δ μ)
  , MonadStateE (LexicalTime μ Ψ) (m δ μ)
  , MonadStateE (DynamicTime μ Ψ) (m δ μ)
  , MonadStep (m δ μ)
  , Ord (LexicalTime μ Ψ)
  , Ord (DynamicTime μ Ψ)
  , Ord (Val δ μ)
  , SSC (m δ μ) RCall
  )

type Analysis δ μ m =
  ( AAM μ
  , Delta δ
  , Δ δ μ
  , MonadCPS δ μ m
  , PartialOrder (SS (m δ μ) RCall)
  , JoinLattice (SS (m δ μ) RCall)
  , JoinLattice (Val δ μ)
  )

mP :: P m -> P δ -> μ -> P (m δ μ)
mP P P _ = P

new :: (Analysis δ μ m) => P δ -> μ -> RName -> m δ μ (Addr μ)
new _ μ x = do
  lτ <- getP $ lexicalTimeP μ ψ
  dτ <- getP $ dynamicTimeP μ ψ
  return $ Addr x lτ dτ

bind :: (Analysis δ μ m) => P δ -> μ -> RName -> Val δ μ -> m δ μ ()
bind δ μ x vD = do
  l <- new δ μ x
  modifyL (envL μ) $ pinsert x l
  modifyL (storeL δ μ) $ pinsertWith (\/) l vD

var :: (Analysis δ μ m) => P δ -> μ -> RName -> m δ μ (Val δ μ)
var δ μ x = do
  e <- getL $ envL μ
  s <- getL $ storeL δ μ
  useMaybeZero $ index s *$ index e $ x

atom :: (Analysis δ μ m) => P δ -> μ -> RAtom -> m δ μ (Val δ μ)
atom δ _ (LitA l) = return $ lit δ l
atom δ μ (Var x) = var δ μ x
atom δ μ (Prim o a) = do
  op δ o <$> atom δ μ a
atom δ μ (Lam xs c) = do
  e <- getP $ envP μ
  lτ <- getP $ lexicalTimeP μ ψ
  return $ clo δ $ Clo xs c e lτ

elimBoolM :: (Analysis δ μ m) => P δ -> Val δ μ -> m δ μ Bool
elimBoolM = msum .: elimBool

elimCloM :: (Analysis δ μ m) => P δ -> Val δ μ -> m δ μ (Clo μ)
elimCloM = msum .: elimClo

tickM :: (Analysis δ μ m) => P δ -> μ -> Int -> m δ μ ()
tickM δ μ cid = do
  _ <- getP $ envP μ
  _ <- getP $ storeP δ μ
  modifyL (lexicalTimeL μ ψ) $ tick (lexical μ) cid
  modifyL (dynamicTimeL μ ψ) $ tick (dynamic μ) cid

call :: (Analysis δ μ m) => P δ -> μ -> P m -> RCall -> m δ μ RCall
call δ μ _ (RCall cid c) = case c of
  If a tc fc -> do
    b <- elimBoolM δ *$ atom δ μ a
    return $ if b then tc else fc
  App fa aes -> do
    Clo xs c' e lτ <- elimCloM δ *$ atom δ μ fa
    vs <- atom δ μ <*$> aes
    xvs <- useMaybeZero $ zipSameLength xs vs
    putP (envP μ) e
    putP (lexicalTimeP μ ψ) lτ
    traverseOn xvs $ uncurry $ bind δ μ
    tickM δ μ cid
    return c'
  Halt a -> return $ RCall cid $ Halt a

-- 'Standard' semantics --
exec :: (Analysis δ μ m) => P δ -> μ -> P m -> RCall -> SS (m δ μ) RCall
exec δ μ m = poiter (mstep $ call δ μ m) . munit (mP m δ μ)

-- Collecting semantics --
execCollect :: (Analysis δ μ m) => P δ -> μ -> P m -> RCall -> SS (m δ μ) RCall
execCollect δ μ m = collect (mstep $ call δ μ m) . munit (mP m δ μ)

type Action a = forall δ μ m. (Analysis δ μ m) => P δ -> μ -> P m -> a -> m δ μ a
none :: Action a
none P _ P = return

execCollectWith :: (Analysis δ μ m) => P δ -> μ -> P m -> Action RCall -> (RCall -> SS (m δ μ) RCall)
execCollectWith δ μ m action = collect (mstep $ action δ μ m *. call δ μ m) . munit (mP m δ μ)

--------
-- GC --
--------

freeVarsLam :: (Analysis δ μ m) => P δ -> μ -> P m -> [RName] -> Call RName RCall -> Set RName
freeVarsLam δ μ m xs c = freeVarsCall δ μ m c \-\ sset xs

freeVarsAtom :: (Analysis δ μ m) => P δ -> μ -> P m -> RAtom -> Set RName
freeVarsAtom _ _ _ (LitA _) = bot
freeVarsAtom _ _ _ (Var x) = ssingleton x
freeVarsAtom δ μ m (Prim _ a) = freeVarsAtom δ μ m a
freeVarsAtom δ μ m (Lam xs c) = freeVarsLam δ μ m xs $ rCall c

freeVarsCall :: (Analysis δ μ m) => P δ -> μ -> P m -> Call RName RCall -> Set RName
freeVarsCall δ μ m (If a tc fc) = freeVarsAtom δ μ m a \/ freeVarsCall δ μ m (rCall tc) \/ freeVarsCall δ μ m (rCall fc)
freeVarsCall δ μ m (App fa aes) = freeVarsAtom δ μ m fa \/ joins (map (freeVarsAtom δ μ m) aes)
freeVarsCall δ μ m (Halt a) = freeVarsAtom δ μ m a

callTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Env μ -> Call RName RCall -> Set (Addr μ)
callTouched δ μ m e c = closureTouched δ μ m e [] c

closureTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Env μ -> [RName] -> Call RName RCall -> Set (Addr μ)
closureTouched δ μ m e xs c = useMaybeSet . index (runEnv e) *$~ freeVarsLam δ μ m xs c

addrTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Store δ μ -> Addr μ -> Set (Addr μ)
addrTouched δ μ m s l = 
  let clos = elimClo δ *$~ useMaybeSet . index (runStore s) $ l
  in clos >>=~ \ (Clo xs c e _) -> closureTouched δ μ m e xs $ rCall c

gc :: Action RCall
gc δ μ m c = do
  e <- getP $ envP μ
  s <- getP $ storeP δ μ
  let live = collect (cextend $ addrTouched δ μ m s) $ callTouched δ μ m e $ rCall c
  modifyL (storeL δ μ) $ ponlyKeys live
  return c
