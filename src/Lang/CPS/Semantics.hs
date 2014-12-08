module Lang.CPS.Semantics where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.Common
import Lang.CPS.Val

type Ψ = LocNum

-- These are the raw constraints that must hold for:
-- - time lτ and dτ
-- - values val
-- - monadic state 𝓈
-- - the transition state space ς
-- - the monad m

type TimeC τ =
  ( Time τ
  , Initial (τ Ψ)
  , Ord (τ Ψ)
  )

type ValC lτ dτ val =
  ( Val val
  , Ord (val lτ dτ Ψ)
  , PartialOrder (val lτ dτ Ψ)
  , JoinLattice (val lτ dτ Ψ)
  )

type StateC val lτ dτ 𝓈 =
  ( HasLens 𝓈 (Lτ lτ Ψ)
  , HasLens 𝓈 (Dτ dτ Ψ)
  , HasLens 𝓈 (Env lτ dτ Ψ)
  , HasLens 𝓈 (Store val lτ dτ Ψ)
  )

type StateSpaceC ς =
  ( PartialOrder (ς SGCall)
  , JoinLattice (ς SGCall)
  , Inject ς
  )

type MonadC val lτ dτ 𝓈 ς m =
  ( Monad m, MonadZero m, MonadPlus m
  , MonadState 𝓈 m
  , MonadStep ς m
  )

-- This type class aids type inference. The functional dependencies tell the
-- type checker that  choices for val, lτ, dτ, 𝓈 and ς are unique for a given
-- m.
class 
  ( TimeC lτ
  , TimeC dτ
  , ValC lτ dτ val
  , StateC val lτ dτ 𝓈
  , StateSpaceC ς
  , MonadC val lτ dτ 𝓈 ς m
  ) => Analysis val lτ dτ 𝓈 ς m | m -> val , m -> lτ , m -> dτ , m -> 𝓈 , m -> ς where

-- Some helper types
type GC m = SGCall -> m ()
type CreateClo lτ dτ m = LocNum -> [SGName] -> SGCall -> m (Clo lτ dτ Ψ)
type TimeFilter = SGCall -> Bool

-- Generate a new address
new :: (Analysis val lτ dτ 𝓈 ς m) => SGName -> m (Addr lτ dτ Ψ)
new x = do
  lτ <- getL view
  dτ <- getL view
  return $ Addr x lτ dτ

-- bind a name to a value in an environment
bind :: (Analysis val lτ dτ 𝓈 ς m) => SGName -> val lτ dτ Ψ -> Map SGName (Addr lτ dτ Ψ) -> m (Map SGName (Addr lτ dτ Ψ))
bind x vD ρ = do
  l <- new x
  modifyL (runStoreL <.> view) $ mapInsertWith (\/) l vD
  return $ mapInsert x l ρ

-- bind a name to a value in _the_ environment
bindM :: (Analysis val lτ dτ 𝓈 ς m) => SGName -> val lτ dτ Ψ -> m ()
bindM x vD = modifyLM (runEnvL <.> view) $ bind x vD

-- the denotation for variables
var :: forall val lτ dτ 𝓈 ς m. (Analysis val lτ dτ 𝓈 ς m) => SGName -> m (val lτ dτ Ψ)
var x = do
  ρ <- getL $ runEnvL <.> view
  σ <- getL $ runStoreL <.> view
  liftMaybeZero $ index σ *$ index ρ $ x

-- the denotation for lambdas
lam :: (Analysis val lτ dτ 𝓈 ς m) => CreateClo lτ dτ m -> LocNum -> [SGName] -> SGCall -> m (val lτ dτ Ψ)
lam createClo = clo ^..: createClo

-- the denotation for the pico syntactic category
pico :: (Analysis val lτ dτ 𝓈 ς m) => SGPico -> m (val lτ dτ Ψ)
pico (Lit l) = return $ lit l
pico (Var x) = var x

-- the denotation for the atom syntactic category
atom :: (Analysis val lτ dτ 𝓈 ς m) => CreateClo lτ dτ m ->  SGAtom -> m (val lτ dτ Ψ)
atom createClo (Stamped i a) = case a of
  Pico p -> pico p
  Prim o ax -> op o ^$ pico ax
  LamF x kx c -> lam createClo i [x, kx] c
  LamK x c -> lam createClo i [x] c

apply :: forall val lτ dτ 𝓈 ς m. (Analysis val lτ dτ 𝓈 ς m) => TimeFilter -> SGCall -> val lτ dτ Ψ -> [val lτ dτ Ψ] -> m SGCall
apply timeFilter c fv avs = do
  Clo cid' xs c' ρ lτ <- mset $ elimClo fv
  xvs <- liftMaybeZero $ zip xs avs
  putL view ρ
  traverseOn xvs $ uncurry $ bindM 
  putL view lτ
  when (timeFilter c) $
    modifyL (getlτL <.> view :: Lens 𝓈 (lτ Ψ)) $ tick cid'
  return c'

call :: forall val lτ dτ 𝓈 ς m. (Analysis val lτ dτ 𝓈 ς m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> SGCall -> m SGCall
call gc createClo ltimeFilter dtimeFilter c = do
  when (dtimeFilter c) $
    modifyL (getdτL <.> view :: Lens 𝓈 (dτ Ψ)) $ tick $ stampedFixID c
  c' <- case stampedFix c of
    Let x a c' -> do
      v <- atom createClo a
      bindM x v
      return c'
    If ax tc fc -> do
      b <- mset . elimBool *$ pico ax
      return $ if b then tc else fc
    AppF fx ax ka -> do
      fv <- pico fx
      av <- pico ax
      kv <- pico ka
      apply ltimeFilter c fv [av, kv]
    AppK kx ax -> do
      kv <- pico kx
      av <- pico ax
      apply ltimeFilter c kv [av]
    Halt _ -> return c
  gc c'
  return c'

-- GC {{{

nogc :: (Monad m) => SGCall -> m ()
nogc _ = return ()

closureTouched :: (TimeC lτ, TimeC dτ) => Clo lτ dτ Ψ -> Set (Addr lτ dτ Ψ)
closureTouched (Clo _ xs c ρ _) = liftMaybeSet . index (runEnv ρ) *$ freeVarsLam xs $ stampedFix c

addrTouched :: (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Map (Addr lτ dτ Ψ) (val lτ dτ Ψ) -> Addr lτ dτ Ψ -> Set (Addr lτ dτ Ψ)
addrTouched σ = closureTouched *. elimClo *. liftMaybeSet . index σ

currClosure :: (Analysis val lτ dτ 𝓈 ς m) => SGCall -> m (Clo lτ dτ Ψ)
currClosure c = do
  ρ <- getL view
  lτ <- getL view
  return $ Clo (LocNum (-1)) [] c ρ lτ

yesgc :: forall val lτ dτ 𝓈 ς m. (Analysis val lτ dτ 𝓈 ς m) => SGCall -> m ()
yesgc c = do
  σ <- getL (runStoreL <.> (view :: Lens 𝓈 (Store val lτ dτ Ψ)))
  live0 <- closureTouched ^$ currClosure c
  let live = collect (extend $ addrTouched $ σ) live0
  modifyL (runStoreL <.> (view :: Lens 𝓈 (Store val lτ dτ Ψ))) $ onlyKeys live

-- }}}

-- CreateClo {{{

linkClo :: (Analysis val lτ dτ 𝓈 ς m) => LocNum -> [SGName] -> SGCall -> m (Clo lτ dτ Ψ)
linkClo cid xs c = do
  ρ <- getL view
  lτ <- getL view
  return $ Clo cid xs c ρ lτ

copyClo :: (Analysis val lτ dτ 𝓈 ς m) => LocNum -> [SGName] -> SGCall -> m (Clo lτ dτ Ψ)
copyClo cid xs c = do
  let ys = toList $ freeVarsLam xs $ stampedFix c
  vs <- var ^*$ ys
  yvs <- liftMaybeZero $ zip ys vs
  ρ <- Env ^$ runKleisliEndo mapEmpty *$ execWriterT $ do
    traverseOn yvs $ tell . KleisliEndo . uncurry bind
  lτ <- getL view
  return $ Clo cid xs c ρ lτ

-- }}}

-- Execution {{{

exec :: (Analysis val lτ dτ 𝓈 ς m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> SGCall -> ς SGCall
exec gc createClo ltimeFilter dtimeFilter = poiter (mstepγ $ call gc createClo ltimeFilter dtimeFilter) . inj

execCollect :: (Analysis val lτ dτ 𝓈 ς m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> SGCall -> ς SGCall
execCollect gc createClo ltimeFilter dtimeFilter = collect (mstepγ $ call gc createClo ltimeFilter dtimeFilter) . inj

-- }}}

-- Parametric Execution {{{

type UniTime τ = W (TimeC τ)
data ExTime where ExTime :: forall τ. UniTime τ -> ExTime

type UniVal val = forall lτ dτ. (TimeC lτ, TimeC dτ) => W (ValC lτ dτ val)
data ExVal where ExVal :: forall val. UniVal val -> ExVal

type UniMonad 𝓈 ς m = 
  forall val lτ dτ. (TimeC lτ, TimeC dτ, ValC lτ dτ val) 
  => W (Analysis val lτ dτ (𝓈 val lτ dτ Ψ) (ς val lτ dτ Ψ) (m val lτ dτ Ψ))
data ExMonad where ExMonad :: forall 𝓈 ς m. UniMonad 𝓈 ς m -> ExMonad

type AllGC         = forall val lτ dτ 𝓈 ς m. (Analysis val lτ dτ 𝓈 ς m) => GC m
type AllCreateClo  = forall val lτ dτ 𝓈 ς m. (Analysis val lτ dτ 𝓈 ς m) => CreateClo lτ dτ m

data Options = Options
  { ltimeOp :: ExTime
  , dtimeOp :: ExTime
  , valOp :: ExVal
  , monadOp :: ExMonad
  , gcOp :: AllGC
  , createCloOp :: AllCreateClo
  , ltimeFilterOp :: TimeFilter
  , dtimeFilterOp :: TimeFilter
  }

data ExSigma where
  ExSigma :: (StateSpaceC ς) => ς SGCall -> ExSigma

runWithOptions :: Options -> SGCall -> ExSigma
runWithOptions o e = case o of
  Options (ExTime (W :: UniTime lτ)) 
          (ExTime (W :: UniTime dτ))
          (ExVal (W :: W (ValC lτ dτ val)))
          (ExMonad (W :: W (Analysis val lτ dτ (𝓈 val lτ dτ Ψ) (ς val lτ dτ Ψ) (m val lτ dτ Ψ))))
          (gc :: GC (m val lτ dτ Ψ))
          (createClo  :: CreateClo lτ dτ (m val lτ dτ Ψ))
          (ltimeFilter :: TimeFilter)
          (dtimeFilter :: TimeFilter) -> 
    ExSigma $ execCollect gc createClo ltimeFilter dtimeFilter e

-- }}}
