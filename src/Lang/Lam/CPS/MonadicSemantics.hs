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

type GC δ μ m = P δ -> μ -> P m -> SGCall -> m δ μ ()
type PolyGC = forall δ μ m. (Analysis δ μ m) => GC δ μ m
type CreateClo δ μ m = P δ -> μ -> P m -> [SGName] -> SGCall -> m δ μ (Clo μ)
type PolyCreateClo = forall δ μ m. (Analysis δ μ m) => CreateClo δ μ m
type TimeFilter = SGCall -> Bool

mP :: P m -> P δ -> μ -> P (m δ μ)
mP P P _ = P

new :: (Analysis δ μ m) => P δ -> μ -> SGName -> m δ μ (Addr μ)
new P μ x = do
  lτ <- getP $ lexicalTimeP μ ψ
  dτ <- getP $ dynamicTimeP μ ψ
  return $ Addr x lτ dτ

bind :: (Analysis δ μ m) => P δ -> μ -> P m -> SGName -> Val δ μ -> Map SGName (Addr μ) -> m δ μ (Map SGName (Addr μ))
bind δ μ _ x vD ρ = do
  l <- new δ μ x
  modifyL (storeL δ μ) $ pinsertWith (\/) l vD
  return $ pinsert x l ρ

bindM :: (Analysis δ μ m) => P δ -> μ -> P m -> SGName -> Val δ μ -> m δ μ ()
bindM δ μ m x vD = modifyLM (envL μ) $ bind δ μ m x vD

var :: (Analysis δ μ m) => P δ -> μ -> SGName -> m δ μ (Val δ μ)
var δ μ x = do
  ρ <- getL $ envL μ
  σ <- getL $ storeL δ μ
  useMaybeZero $ index σ *$ index ρ $ x

lam :: (Analysis δ μ m) => P δ -> μ -> P m -> CreateClo δ μ m -> [SGName] -> SGCall -> m δ μ (Val δ μ)
lam δ μ m createClo = map (clo δ) .: createClo δ μ m

pico :: (Analysis δ μ m) => P δ -> μ -> SGPico -> m δ μ (Val δ μ)
pico δ _ (Lit l) = return $ lit δ l
pico δ μ (Var x) = var δ μ x

atom :: (Analysis δ μ m) => P δ -> μ -> P m -> CreateClo δ μ m ->  SGAtom -> m δ μ (Val δ μ)
atom δ μ P _ (Pico p) = pico δ μ p
atom δ μ P _ (Prim o ax) = op δ o <$> pico δ μ ax
atom δ μ m createClo (LamF x kx c) = lam δ μ m createClo [x, kx] c
atom δ μ m createClo (LamK x c) = lam δ μ m createClo [x] c

elimBoolM :: (Analysis δ μ m) => P δ -> Val δ μ -> m δ μ Bool
elimBoolM = msum .: elimBool

elimCloM :: (Analysis δ μ m) => P δ -> Val δ μ -> m δ μ (Clo μ)
elimCloM = msum .: elimClo

tickM :: (Analysis δ μ m) => P δ -> μ -> LocNum -> m δ μ ()
tickM _ μ cid = do
  modifyL (lexicalTimeL μ ψ) $ tick (lexical μ) cid
  lτ <- getP $ lexicalTimeP μ ψ
  modifyL (dynamicTimeL μ ψ) $ tick (dynamic μ) $ DynamicMoment cid lτ

apply :: (Analysis δ μ m) => P δ -> μ -> P m -> Val δ μ -> [Val δ μ] -> m δ  μ SGCall
apply δ μ m fv avs = do
  Clo xs c' ρ lτ <- elimCloM δ fv
  xvs <- useMaybeZero $ zipSameLength xs avs
  putP (envP μ) ρ
  traverseOn xvs $ uncurry $ bindM δ μ m
  putP (lexicalTimeP μ ψ) lτ
  return c'

call :: (Analysis δ μ m) => P δ -> μ -> P m -> GC δ μ m -> CreateClo δ μ m -> TimeFilter -> SGCall -> m δ μ SGCall
call δ μ m gc createClo timeFilter c = do
  when (timeFilter c) $
    tickM δ μ $ stampedFixID c
  c' <- case stampedFix c of
    Let x a c' -> do
      v <- atom δ μ m createClo a
      bindM δ μ m x v
      return c'
    If ax tc fc -> do
      b <- elimBoolM δ *$ pico δ μ ax
      return $ if b then tc else fc
    AppF fx ax ka -> do
      fv <- pico δ μ fx
      av <- pico δ μ ax
      kv <- pico δ μ ka
      apply δ μ m fv [av, kv]
    AppK kx ax -> do
      kv <- pico δ μ kx
      av <- pico δ μ ax
      apply δ μ m kv [av]
    Halt _ -> return c
  gc δ μ m c'
  return c'

exec :: (Analysis δ μ m) => P δ -> μ -> P m -> GC δ μ m -> CreateClo δ μ m -> TimeFilter -> SGCall -> SS (m δ μ) SGCall
exec δ μ m gc createClo timeFilter = poiter (mstep $ call δ μ m gc createClo timeFilter) . munit (mP m δ μ)

execCollect :: (Analysis δ μ m) => P δ -> μ -> P m -> GC δ μ m -> CreateClo δ μ m -> TimeFilter -> SGCall -> SS (m δ μ) SGCall
execCollect δ μ m gc createClo timeFilter = collect (mstep $ call δ μ m gc createClo timeFilter) . munit (mP m δ μ)

-- Computing Free Vars {{{

freeVarsLam :: [SGName] -> PreCall SGName SGCall -> Set SGName
freeVarsLam xs c = freeVarsCall c \-\ sset xs

freeVarsPico :: SGPico -> Set SGName
freeVarsPico (Lit _) = bot
freeVarsPico (Var x) = cunit x

freeVarsAtom :: SGAtom -> Set SGName
freeVarsAtom (Pico p) = freeVarsPico p
freeVarsAtom (Prim _ ax) = freeVarsPico ax
freeVarsAtom (LamF x kx c) = freeVarsLam [x, kx] $ stampedFix c
freeVarsAtom (LamK x c) = freeVarsLam [x] $ stampedFix c

freeVarsCall :: PreCall SGName SGCall -> Set SGName
freeVarsCall (Let x a c) = freeVarsAtom a \/ (freeVarsCall (stampedFix c) \-\ cunit x)
freeVarsCall (If ax tc fc) = freeVarsPico ax \/ joins (map (freeVarsCall . stampedFix) [tc, fc])
freeVarsCall (AppF fx ax kx) = joins $ map (freeVarsPico) [fx, ax, kx]
freeVarsCall (AppK kx ax) = joins $ map (freeVarsPico) [kx, ax]
freeVarsCall (Halt ax) = freeVarsPico ax

-- }}}

-- GC {{{

nogc :: PolyGC
nogc _ _ _ _ = return ()

closureTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Clo μ -> Set (Addr μ)
closureTouched _ _ _ (Clo xs c ρ _) = useMaybeSet . index (runEnv ρ) *$ freeVarsLam xs $ stampedFix c

addrTouched :: (Analysis δ μ m) => P δ -> μ -> P m -> Store δ μ -> Addr μ -> Set (Addr μ)
addrTouched δ μ m σ = closureTouched δ μ m *. elimClo δ *. useMaybeSet . index (runStore σ)

currClosure :: (Analysis δ μ m) => P δ -> μ -> P m -> SGCall -> m δ μ (Clo μ)
currClosure _ μ _ c = do
  ρ <- getP $ envP μ
  lτ <- getP $ lexicalTimeP μ ψ
  return $ Clo [] c ρ lτ

yesgc :: PolyGC
yesgc δ μ m c = do
  σ <- getP $ storeP δ μ
  initial <- closureTouched δ μ m <$> currClosure δ μ m c
  let live = collect (extend $ addrTouched δ μ m σ) initial
  modifyL (storeL δ μ) $ ponlyKeys live

-- }}}

-- CreateClo {{{

linkClo :: PolyCreateClo
linkClo _ μ _ xs c = do
  ρ <- getP $ envP μ
  lτ <- getP $ lexicalTimeP μ ψ
  return $ Clo xs c ρ lτ

copyClo :: PolyCreateClo
copyClo δ μ m xs c = do
  let ys = toList $ freeVarsLam xs $ stampedFix c
  vs <- mapM (var δ μ) ys
  yvs <- useMaybeZero $ zipSameLength ys vs
  ρ' <- Env <$> runKleisliEndo pempty *$ execWriterT $ do
    traverseOn yvs $ uncurry $ \ y v ->
      tell $ KleisliEndo $ bind δ μ m y v
  lτ <- getP $ lexicalTimeP μ ψ
  return $ Clo xs c ρ' lτ

-- }}}
