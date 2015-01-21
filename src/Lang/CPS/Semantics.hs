module Lang.CPS.Semantics where

import FP
import MAAM
import Lang.CPS.Syntax
import Lang.Common
import Lang.CPS.StateSpace

type Ψ = LocNum

-- These are the raw constraints that must hold for:
-- - time lτ and dτ
-- - values val
-- - the transition state space ς
-- - the monad m

type TimeC τ =
  ( Time τ
  , Initial (τ Ψ)
  , Ord (τ Ψ)
  , Pretty (τ Ψ)
  )

type ValC lτ dτ val =
  ( Val lτ dτ Ψ (val lτ dτ Ψ)
  , Ord (val lτ dτ Ψ)
  , PartialOrder (val lτ dτ Ψ)
  , JoinLattice (val lτ dτ Ψ)
  , Pretty (val lτ dτ Ψ)
  )

type StateSpaceC ς =
  ( PartialOrder (ς SGCall)
  , JoinLattice (ς SGCall)
  , Inject ς
  , Pretty (ς SGCall)
  )

type MonadC val lτ dτ ς m =
  ( Monad m, MonadZero m, MonadPlus m
  , MonadState (𝒮 val lτ dτ Ψ) m
  , MonadStep ς m
  )

-- This type class aids type inference. The functional dependencies tell the
-- type checker that  choices for val, lτ, dτ, 𝓈 and ς are unique for a given
-- m.
class 
  ( TimeC lτ
  , TimeC dτ
  , ValC lτ dτ val
  , StateSpaceC ς
  , MonadC val lτ dτ ς m
  ) => Analysis val lτ dτ ς m | m -> val , m -> lτ , m -> dτ , m -> ς where

-- Some helper types
type GC m = SGCall -> m ()
type CreateClo lτ dτ m = LocNum -> [SGName] -> SGCall -> m (Clo lτ dτ Ψ)
type TimeFilter = SGCall -> Bool

-- Generate a new address
new :: (Analysis val lτ dτ ς m) => SGName -> m (Addr lτ dτ Ψ)
new x = do
  lτ <- getL 𝓈lτL
  dτ <- getL 𝓈dτL
  return $ Addr x lτ dτ

-- bind a name to a value in an environment
bind :: (Analysis val lτ dτ ς m) => SGName -> val lτ dτ Ψ -> Map SGName (Addr lτ dτ Ψ) -> m (Map SGName (Addr lτ dτ Ψ))
bind x vD ρ = do
  l <- new x
  modifyL 𝓈σL $ mapInsertWith (\/) l vD
  return $ mapInsert x l ρ

-- bind a name to a value in _the_ environment
bindM :: (Analysis val lτ dτ ς m) => SGName -> val lτ dτ Ψ -> m ()
bindM x vD = modifyLM 𝓈ρL $ bind x vD

-- the denotation for variables
var :: forall val lτ dτ ς m. (Analysis val lτ dτ ς m) => SGName -> m (val lτ dτ Ψ)
var x = do
  ρ <- getL 𝓈ρL
  σ <- getL 𝓈σL
  liftMaybeZero $ index σ *$ index ρ $ x

-- the denotation for lambdas
lam :: (Analysis val lτ dτ ς m) => CreateClo lτ dτ m -> LocNum -> [SGName] -> SGCall -> m (val lτ dτ Ψ)
lam createClo = clo ^..: createClo

-- the denotation for the pico syntactic category
pico :: (Analysis val lτ dτ ς m) => SGPico -> m (val lτ dτ Ψ)
pico (Lit l) = return $ lit l
pico (Var x) = var x

-- the denotation for the atom syntactic category
atom :: (Analysis val lτ dτ ς m) => CreateClo lτ dτ m ->  SGAtom -> m (val lτ dτ Ψ)
atom createClo (Stamped i a) = case a of
  Pico p -> pico p
  Prim o ax -> op o ^$ pico ax
  LamF x kx c -> lam createClo i [x, kx] c
  LamK x c -> lam createClo i [x] c

apply :: (Analysis val lτ dτ ς m) => TimeFilter -> SGCall -> val lτ dτ Ψ -> [val lτ dτ Ψ] -> m SGCall
apply timeFilter c fv avs = do
  Clo cid' xs c' ρ lτ <- mset $ elimClo fv
  xvs <- liftMaybeZero $ zip xs avs
  putL 𝓈ρL ρ
  traverseOn xvs $ uncurry $ bindM 
  putL 𝓈lτL lτ
  when (timeFilter c) $
    modifyL 𝓈lτL $ tick cid'
  return c'

call :: (Analysis val lτ dτ ς m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> SGCall -> m SGCall
call gc createClo ltimeFilter dtimeFilter c = do
  when (dtimeFilter c) $
    modifyL 𝓈dτL $ tick $ stampedFixID c
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
closureTouched (Clo _ xs c ρ _) = liftMaybeSet . index ρ *$ freeVarsLam xs $ stampedFix c

addrTouched :: (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Map (Addr lτ dτ Ψ) (val lτ dτ Ψ) -> Addr lτ dτ Ψ -> Set (Addr lτ dτ Ψ)
addrTouched σ = closureTouched *. elimClo *. liftMaybeSet . index σ

currClosure :: (Analysis val lτ dτ ς m) => SGCall -> m (Clo lτ dτ Ψ)
currClosure c = do
  ρ <- getL 𝓈ρL
  lτ <- getL 𝓈lτL
  return $ Clo (LocNum (-1)) [] c ρ lτ

yesgc :: forall val lτ dτ ς m. (Analysis val lτ dτ ς m) => SGCall -> m ()
yesgc c = do
  σ <- getL 𝓈σL
  live0 <- closureTouched ^$ currClosure c
  let live = collect (extend $ addrTouched $ σ) live0
  modifyL 𝓈σL $ onlyKeys live

-- }}}

-- CreateClo {{{

linkClo :: (Analysis val lτ dτ ς m) => LocNum -> [SGName] -> SGCall -> m (Clo lτ dτ Ψ)
linkClo cid xs c = do
  ρ <- getL 𝓈ρL
  lτ <- getL 𝓈lτL
  return $ Clo cid xs c ρ lτ

copyClo :: (Analysis val lτ dτ ς m) => LocNum -> [SGName] -> SGCall -> m (Clo lτ dτ Ψ)
copyClo cid xs c = do
  let ys = toList $ freeVarsLam xs $ stampedFix c
  vs <- var ^*$ ys
  yvs <- liftMaybeZero $ zip ys vs
  ρ <- runKleisliEndo mapEmpty *$ execWriterT $ do
    traverseOn yvs $ tell . KleisliEndo . uncurry bind
  lτ <- getL 𝓈lτL
  return $ Clo cid xs c ρ lτ

-- }}}

-- Execution {{{

exec :: (Analysis val lτ dτ ς m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> SGCall -> ς SGCall
exec gc createClo ltimeFilter dtimeFilter = poiter (mstepγ $ call gc createClo ltimeFilter dtimeFilter) . inj

execCollect :: (Analysis val lτ dτ ς m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> SGCall -> ς SGCall
execCollect gc createClo ltimeFilter dtimeFilter = collect (mstepγ $ call gc createClo ltimeFilter dtimeFilter) . inj

-- }}}

-- Parametric Execution {{{

type UniTime τ = W (TimeC τ)
data ExTime where ExTime :: forall τ. UniTime τ -> ExTime

type UniVal val = forall lτ dτ. (TimeC lτ, TimeC dτ) => W (ValC lτ dτ val)
data ExVal where ExVal :: forall val. UniVal val -> ExVal

type UniMonad ς m = 
  forall val lτ dτ. (TimeC lτ, TimeC dτ, ValC lτ dτ val) 
  => W (Analysis val lτ dτ (ς val lτ dτ Ψ) (m val lτ dτ Ψ))
data ExMonad where ExMonad :: forall ς m. UniMonad ς m -> ExMonad

newtype AllGC = AllGC { runAllGC :: forall val lτ dτ ς m. (Analysis val lτ dτ ς m) => GC m }
newtype AllCreateClo  = AllCreateClo { runAllCreateClo :: forall val lτ dτ ς m. (Analysis val lτ dτ ς m) => CreateClo lτ dτ m }

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
          (ExMonad (W :: W (Analysis val lτ dτ (ς val lτ dτ Ψ) (m val lτ dτ Ψ))))
          (AllGC (gc :: GC (m val lτ dτ Ψ)))
          (AllCreateClo (createClo  :: CreateClo lτ dτ (m val lτ dτ Ψ)))
          (ltimeFilter :: TimeFilter)
          (dtimeFilter :: TimeFilter) -> 
    ExSigma $ execCollect gc createClo ltimeFilter dtimeFilter e

-- }}}
