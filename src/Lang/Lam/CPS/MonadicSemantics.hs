module Lang.Lam.CPS.MonadicSemantics where

import FP
import MAAM
import Lang.Lam.CPS.Syntax
import Lang.Lam.CPS.Classes.Delta
import Lang.Lam.Syntax (SGName, LocNum)

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
  , SSC (m δ μ) SGCall
  )

type Analysis δ μ m =
  ( AAM μ
  , Delta δ
  , Δ δ μ
  , MonadCPS δ μ m
  , PartialOrder (SS (m δ μ) SGCall)
  , JoinLattice (SS (m δ μ) SGCall)
  , JoinLattice (Val δ μ)
  )

data M where
  M :: (Analysis δ μ m) => P δ -> P μ -> P m -> M

mP :: P m -> P δ -> μ -> P (m δ μ)
mP P P _ = P

new :: (Analysis δ μ m) => P δ -> μ -> SGName -> m δ μ (Addr μ)
new _ μ x = do
  lτ <- getP $ lexicalTimeP μ ψ
  dτ <- getP $ dynamicTimeP μ ψ
  return $ Addr x lτ dτ

bind :: (Analysis δ μ m) => P δ -> μ -> SGName -> Val δ μ -> m δ μ ()
bind δ μ x vD = do
  l <- new δ μ x
  modifyL (envL μ) $ pinsert x l
  modifyL (storeL δ μ) $ pinsertWith (\/) l vD

var :: (Analysis δ μ m) => P δ -> μ -> SGName -> m δ μ (Val δ μ)
var δ μ x = do
  e <- getL $ envL μ
  s <- getL $ storeL δ μ
  useMaybeZero $ index s *$ index e $ x

lam :: (Analysis δ μ m) => P δ -> μ -> [SGName] -> SGCall -> m δ μ (Val δ μ)
lam δ μ xs c = do
  e <- getP $ envP μ
  lτ <- getP $ lexicalTimeP μ ψ
  return $ clo δ $ Clo xs c e lτ

pico :: (Analysis δ μ m) => P δ -> μ -> SGPico -> m δ μ (Val δ μ)
pico δ _ (Lit l) = return $ lit δ l
pico δ μ (Var x) = var δ μ x

atom :: (Analysis δ μ m) => P δ -> μ -> SGAtom -> m δ μ (Val δ μ)
atom δ μ (Pico p) = pico δ μ p
atom δ μ (Prim o ax) = do
  op δ o <$> pico δ μ ax
atom δ μ (LamF x kx c) = lam δ μ [x, kx] c
atom δ μ (LamK x c) = lam δ μ [x] c

elimBoolM :: (Analysis δ μ m) => P δ -> Val δ μ -> m δ μ Bool
elimBoolM = msum .: elimBool

elimCloM :: (Analysis δ μ m) => P δ -> Val δ μ -> m δ μ (Clo μ)
elimCloM = msum .: elimClo

tickM :: (Analysis δ μ m) => P δ -> μ -> LocNum -> m δ μ ()
tickM δ μ cid = do
  _ <- getP $ envP μ
  _ <- getP $ storeP δ μ
  modifyL (lexicalTimeL μ ψ) $ tick (lexical μ) cid
  lτ <- getP (lexicalTimeP μ ψ)
  modifyL (dynamicTimeL μ ψ) $ tick (dynamic μ) $ DynamicMoment cid lτ

apply :: (Analysis δ μ m) => P δ -> μ -> P m -> Val δ μ -> [Val δ μ] -> m δ  μ SGCall
apply δ μ _ fv avs = do
  Clo xs c' e lτ <- elimCloM δ fv
  xvs <- useMaybeZero $ zipSameLength xs avs
  putP (envP μ) e
  putP (lexicalTimeP μ ψ) lτ
  traverseOn xvs $ \ (x,v) -> 
    bind δ μ x v
  return c'

call :: (Analysis δ μ m) => P δ -> μ -> P m -> SGCall -> m δ μ SGCall
call δ μ m (StampedFix cid c) = case c of
  Let x a c' -> do
    tickM δ μ cid
    v <- atom δ μ a
    bind δ μ x v
    return c'
  If ax tc fc -> do
    tickM δ μ cid
    b <- elimBoolM δ *$ pico δ μ ax
    return $ if b then tc else fc
  AppF fx ax ka -> do
    tickM δ μ cid
    fv <- pico δ μ fx
    av <- pico δ μ ax
    kv <- atom δ μ ka
    apply δ μ m fv [av, kv]
  AppK kx ax -> do
    tickM δ μ cid
    kv <- pico δ μ kx
    av <- pico δ μ ax
    apply δ μ m kv [av]
  Halt a -> return $ StampedFix cid $ Halt a

-- 'Standard' semantics --
exec :: (Analysis δ μ m) => P δ -> μ -> P m -> SGCall -> SS (m δ μ) SGCall
exec δ μ m = poiter (mstep $ call δ μ m) . munit (mP m δ μ)

-- Collecting semantics --
execCollect :: (Analysis δ μ m) => P δ -> μ -> P m -> SGCall -> SS (m δ μ) SGCall
execCollect δ μ m = collect (mstep $ call δ μ m) . munit (mP m δ μ)

type Action a = forall δ μ m. (Analysis δ μ m) => P δ -> μ -> P m -> a -> m δ μ a
naive :: Action a
naive P _ P = return

execCollectWith :: (Analysis δ μ m) => P δ -> μ -> P m -> Action SGCall -> SGCall -> SS (m δ μ) SGCall
execCollectWith δ μ m action = collect (mstep $ action δ μ m *. call δ μ m) . munit (mP m δ μ)

-- GC {{{

freeVarsLam :: (Analysis δ μ m) => P δ -> μ -> P m -> [SGName] -> PreCall SGName SGCall -> Set SGName
freeVarsLam δ μ m xs c = freeVarsCall δ μ m c \-\ sset xs

freeVarsPico :: (Analysis δ μ m) => P δ -> μ -> P m -> SGPico -> Set SGName
freeVarsPico _ _ _ (Lit _) = bot
freeVarsPico _ _ _ (Var x) = cunit x

freeVarsAtom :: (Analysis δ μ m) => P δ -> μ -> P m -> SGAtom -> Set SGName
freeVarsAtom δ μ m (Pico p) = freeVarsPico δ μ m p
freeVarsAtom δ μ m (Prim _ ax) = freeVarsPico δ μ m ax
freeVarsAtom δ μ m (LamF x kx c) = freeVarsLam δ μ m [x, kx] $ stampedFix c
freeVarsAtom δ μ m (LamK x c) = freeVarsLam δ μ m [x] $ stampedFix c

freeVarsCall :: (Analysis δ μ m) => P δ -> μ -> P m -> PreCall SGName SGCall -> Set SGName
freeVarsCall δ μ m (Let x a c) = freeVarsAtom δ μ m a \/ (freeVarsCall δ μ m (stampedFix c) \-\ cunit x)
freeVarsCall δ μ m (If ax tc fc) = freeVarsPico δ μ m ax \/ joins (map (freeVarsCall δ μ m . stampedFix) [tc, fc])
freeVarsCall δ μ m (AppF fx ax kx) = joins (map (freeVarsPico δ μ m) [fx, ax]) \/ freeVarsAtom δ μ m kx
freeVarsCall δ μ m (AppK kx ax) = joins $ map (freeVarsPico δ μ m) [kx, ax]
freeVarsCall δ μ m (Halt ax) = freeVarsPico δ μ m ax

callTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Env μ -> PreCall SGName SGCall -> Set (Addr μ)
callTouched δ μ m e c = closureTouched δ μ m e [] c

closureTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Env μ -> [SGName] -> PreCall SGName SGCall -> Set (Addr μ)
closureTouched δ μ m e xs c = useMaybeSet . index (runEnv e) *$ freeVarsLam δ μ m xs c

addrTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Store δ μ -> Addr μ -> Set (Addr μ)
addrTouched δ μ m s l = 
  let clos = elimClo δ *$ useMaybeSet . index (runStore s) $ l
  in clos >>= \ (Clo xs c e _) -> closureTouched δ μ m e xs $ stampedFix c

gc :: (Analysis δ μ m) => P δ -> μ -> P m -> SGCall -> m δ μ SGCall
gc δ μ m c = do
  e <- getP $ envP μ
  s <- getP $ storeP δ μ
  let live = collect (extend $ addrTouched δ μ m s) (callTouched δ μ m e $ stampedFix c)
  modifyL (storeL δ μ) $ ponlyKeys live
  return c

-- }}}
