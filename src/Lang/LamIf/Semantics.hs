module Lang.LamIf.Semantics where

import FP
import MAAM
import Lang.LamIf.Syntax hiding (PreExp(..))
import Lang.LamIf.CPS
import Lang.LamIf.StateSpace

type Ψ = LocNum

-- These are the raw constraints that must hold for:
-- - time lτ and dτ
-- - values val
-- - the monad m

type TimeC τ =
  ( Time Ψ τ
  , Bot τ
  , Ord τ
  , Pretty τ
  )

type ValC lτ dτ val =
  ( Val lτ dτ val
  , Ord val
  , PartialOrder val
  , JoinLattice val
  , Difference val
  , Pretty val
  )

type MonadC val lτ dτ m =
  ( Monad m, MonadBot m, MonadPlus m
  , MonadState (𝒮 val lτ dτ) m
  )

-- This type class aids type inference. The functional dependencies tell the
-- type checker that  choices for val, lτ, dτ and 𝓈 are unique for a given
-- m.
class 
  ( TimeC lτ
  , TimeC dτ
  , ValC lτ dτ val
  , MonadC val lτ dτ m
  ) => Analysis val lτ dτ m | m -> val , m -> lτ , m -> dτ where

-- Some helper types
type GC m = Call -> m ()
type CreateClo lτ dτ m = LocNum -> [Name] -> Call -> m (Clo lτ dτ)
type TimeFilter = Call -> Bool

-- Generate a new address
new :: (Analysis val lτ dτ m) => Name -> m (Addr lτ dτ)
new x = do
  lτ <- getL 𝓈lτL
  dτ <- getL 𝓈dτL
  return $ Addr x lτ dτ

-- bind a name to a value in an environment
bind :: (Analysis val lτ dτ m) => Name -> val -> Map Name (Addr lτ dτ) -> m (Map Name (Addr lτ dτ))
bind x vD ρ = do
  l <- new x
  modifyL 𝓈σL $ mapInsertWith (\/) l vD
  return $ mapInsert x l ρ

-- bind a name to a value in _the_ environment
bindM :: (Analysis val lτ dτ m) => Name -> val -> m ()
bindM x vD = do
  ρ <- getL 𝓈ρL
  ρ' <- bind x vD ρ
  putL 𝓈ρL ρ'

-- rebinds the value assigned to a name
rebind :: (Analysis val lτ dτ m) => Name -> val -> m ()
rebind x vD = do
  ρ <- getL 𝓈ρL
  let l = ρ #! x
  modifyL 𝓈σL $ mapInsert l vD

-- rebinds the value assigned to a pico if it is a name
rebindPico :: (Analysis val lτ dτ m) => PrePico Name -> val -> m ()
rebindPico (Lit _) _ = return ()
rebindPico (Var x) vD = rebind x vD

-- the denotation for addresses
addr :: (Analysis val lτ dτ m) => Addr lτ dτ -> m val
addr 𝓁 = do
  σ <- getL 𝓈σL
  maybeZero $ σ # 𝓁

-- the denotation for variables
var :: (Analysis val lτ dτ m) => Name -> m val
var x = do
  ρ <- getL 𝓈ρL
  𝓁 <- maybeZero $ ρ # x
  addr 𝓁

-- the denotation for lambdas
lam :: (Analysis val lτ dτ m) => CreateClo lτ dτ m -> LocNum -> [Name] -> Call -> m val
lam createClo = clo ^..: createClo

-- the partial denotation for pico (for storing in values)
picoRef :: (Analysis val lτ dτ m) => Pico -> m (PicoVal lτ dτ)
picoRef (Lit l) = return $ LitPicoVal l
picoRef (Var x) = do
  ρ <- getL 𝓈ρL
  AddrPicoVal ^$ maybeZero $ ρ # x

picoVal :: (Analysis val lτ dτ m) => PicoVal lτ dτ -> m val
picoVal (LitPicoVal l) = return $ lit l
picoVal (AddrPicoVal 𝓁) = addr 𝓁

-- the denotation for the pico syntactic category
pico :: (Analysis val lτ dτ m) => Pico -> m val
pico = picoVal *. picoRef

-- the denotation for the atom syntactic category
atom :: (Analysis val lτ dτ m) => CreateClo lτ dτ m -> Atom -> m val
atom createClo a = case stamped a of
  Pico p -> pico p
  Prim o a1 a2 -> return (binop $ lbinOpOp o) <@> pico a1 <@> pico a2
  LamF x kx c -> lam createClo (stampedID a) [x, kx] c
  LamK x c -> lam createClo (stampedID a) [x] c
  Tup p1 p2 -> pure (curry tup) <@> picoRef p1 <@> picoRef p2
  Pi1 p -> picoVal *. fst ^. mset . elimTup *$ pico p
  Pi2 p -> picoVal *. snd ^. mset . elimTup *$ pico p

apply :: (Analysis val lτ dτ m) => TimeFilter -> Call -> PrePico Name -> val -> [val] -> m Call
apply timeFilter c fx fv avs = do
  fclo@(Clo cid' xs c' ρ lτ) <- mset $ elimClo fv
  rebindPico fx $ clo fclo
  xvs <- maybeZero $ zip xs avs
  putL 𝓈ρL ρ
  traverseOn xvs $ uncurry $ bindM 
  putL 𝓈lτL lτ
  when (timeFilter c) $
    modifyL 𝓈lτL $ tick cid'
  return c'

call :: (Analysis val lτ dτ m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> Call -> m Call
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
      rebindPico ax $ lit $ B b
      return $ if b then tc else fc
    AppF fx ax ka -> do
      fv <- pico fx
      av <- pico ax
      kv <- pico ka
      apply ltimeFilter c fx fv [av, kv]
    AppK kx ax -> do
      kv <- pico kx
      av <- pico ax
      apply ltimeFilter c kx kv [av]
    Halt _ -> return c
  gc c'
  return c'

onlyStuck :: (MonadStep ς m,  Analysis val lτ dτ m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> Call -> m Call
onlyStuck gc createClo ltimeFilter dtimeFilter e = do
  e' <- call gc createClo ltimeFilter dtimeFilter e
  if e == e' then return e else mbot

-- Execution {{{

type StateSpaceC ς' =
  ( PartialOrder (ς' Call)
  , JoinLattice (ς' Call)
  , Difference (ς' Call)
  , Pretty (ς' Call)
  )

class (MonadStep ς m, Inject ς, Isomorphism (ς Call) (ς' Call), StateSpaceC ς') => Execution ς ς' m | m -> ς, m -> ς'

liftς :: (Execution ς ς' m) => (Call -> m Call) -> (ς' Call -> ς' Call)
liftς f = isoto . mstepγ f . isofrom

injectς :: forall ς ς' a. (Inject ς, Isomorphism (ς a) (ς' a)) => P ς -> a -> ς' a
injectς P = isoto . (inj :: a -> ς a)

execς :: forall val lτ dτ m ς ς'. (Analysis val lτ dτ m, Execution ς ς' m) => 
  GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> Call -> ς' Call
execς gc createClo ltimeFilter dtimeFilter = poiter (liftς $ call gc createClo ltimeFilter dtimeFilter) . injectς (P :: P ς)

execCollect :: forall val lτ dτ m ς ς'. (Analysis val lτ dτ m, Execution ς ς' m) => 
  GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> Call -> ς' Call
execCollect gc createClo ltimeFilter dtimeFilter = collect (liftς $ call gc createClo ltimeFilter dtimeFilter) . injectς (P :: P ς)

execCollectHistory :: forall val lτ dτ m ς ς'. (Analysis val lτ dτ m, Execution ς ς' m) => 
  GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> Call -> [ς' Call]
execCollectHistory gc createClo ltimeFilter dtimeFilter = collectHistory (liftς $ call gc createClo ltimeFilter dtimeFilter) . injectς (P :: P ς)

execCollectDiffs :: forall val lτ dτ m ς ς'. (Analysis val lτ dτ m, Execution ς ς' m) =>
  GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> Call -> [ς' Call]
execCollectDiffs gc createClo ltimeFilter dtimeFilter = collectDiffs (liftς $ call gc createClo ltimeFilter dtimeFilter) . injectς (P :: P ς)

execOnlyStuck :: (Analysis val lτ dτ m, Execution ς ς' m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> Call -> ς' Call
execOnlyStuck gc createClo ltimeFilter dtimeFilter = 
    liftς (onlyStuck gc createClo ltimeFilter dtimeFilter) 
  . execCollect gc createClo ltimeFilter dtimeFilter

-- }}}

-- GC {{{

nogc :: (Monad m) => Call -> m ()
nogc _ = return ()

yesgc :: (Analysis val lτ dτ m) => Call -> m ()
yesgc c = do
  ρ <- getL 𝓈ρL
  σ <- getL 𝓈σL
  let live0 = callTouched ρ $ freeVarsLam empty [] c
  let live = collect (extend $ addrTouched σ) live0
  modifyL 𝓈σL $ onlyKeys live

callTouched :: (TimeC lτ, TimeC dτ) => Env lτ dτ -> Set Name -> Set (Addr lτ dτ)
callTouched ρ xs = maybeSet . index ρ *$ xs

closureTouched :: (TimeC lτ, TimeC dτ) => Clo lτ dτ -> Set (Addr lτ dτ)
closureTouched (Clo _ xs c ρ _) = callTouched ρ $ freeVarsLam empty xs c

picoValTouched :: (TimeC lτ, TimeC dτ) => PicoVal lτ dτ -> Set (Addr lτ dτ)
picoValTouched (LitPicoVal _) = empty
picoValTouched (AddrPicoVal 𝓁) = single 𝓁

tupleTouched :: (TimeC lτ, TimeC dτ) => (PicoVal lτ dτ, PicoVal lτ dτ) -> Set (Addr lτ dτ)
tupleTouched (pv1, pv2) = picoValTouched pv1 \/ picoValTouched pv2

addrTouched :: (TimeC lτ, TimeC dτ, ValC lτ dτ val) => Map (Addr lτ dτ) val -> Addr lτ dτ -> Set (Addr lτ dτ)
addrTouched σ 𝓁 = do
  v <- maybeSet $ σ # 𝓁
  msum
    [ closureTouched *$ elimClo v 
    , tupleTouched *$ elimTup v
    ]

-- }}}

-- CreateClo {{{

linkClo :: (Analysis val lτ dτ m) => LocNum -> [Name] -> Call -> m (Clo lτ dτ)
linkClo cid xs c = do
  ρ <- getL 𝓈ρL
  lτ <- getL 𝓈lτL
  return $ Clo cid xs c ρ lτ

copyClo :: (Analysis val lτ dτ m) => LocNum -> [Name] -> Call -> m (Clo lτ dτ)
copyClo cid xs c = do
  let ys = toList $ freeVarsLam empty xs c
  vs <- var ^*$ ys
  yvs <- maybeZero $ zip ys vs
  ρ <- runKleisliEndo mapEmpty *$ execWriterT $ do
    traverseOn yvs $ tell . KleisliEndo . uncurry bind
  lτ <- getL 𝓈lτL
  return $ Clo cid xs c ρ lτ

-- }}}

-- Parametric Execution {{{

type UniTime τ = W (TimeC τ)
data ExTime where ExTime :: forall τ. UniTime τ -> ExTime

type UniVal val = forall lτ dτ. (TimeC lτ, TimeC dτ) => W (ValC lτ dτ (val lτ dτ))
data ExVal where ExVal :: forall val. UniVal val -> ExVal

type UniMonad ς ς' m = 
  forall val lτ dτ. (TimeC lτ, TimeC dτ, ValC lτ dτ val) 
  => W (Analysis val lτ dτ (m val lτ dτ), Execution (ς val lτ dτ) (ς' val lτ dτ) (m val lτ dτ))
data ExMonad where 
  ExMonad :: forall ς ς' m. 
       UniMonad ς ς' m 
    -> ExMonad

newtype AllGC = AllGC { runAllGC :: forall val lτ dτ m. (Analysis val lτ dτ m) => GC m }
newtype AllCreateClo  = AllCreateClo { runAllCreateClo :: forall val lτ dτ m. (Analysis val lτ dτ m) => CreateClo lτ dτ m }

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

withOptions :: forall a. Options -> ((Analysis val lτ dτ m, Execution ς ς' m) => GC m -> CreateClo lτ dτ m -> TimeFilter -> TimeFilter -> a) -> a
withOptions o f = case o of
  Options (ExTime (W :: UniTime lτ)) 
          (ExTime (W :: UniTime dτ))
          (ExVal (W :: W (ValC lτ dτ (val lτ dτ))))
          (ExMonad (W :: W ( Analysis (val lτ dτ) lτ dτ (m (val lτ dτ) lτ dτ)
                           , Execution (ς (val lτ dτ) lτ dτ) (ς' (val lτ dτ) lτ dτ) (m (val lτ dτ) lτ dτ))))
          (AllGC (gc :: GC (m (val lτ dτ) lτ dτ)))
          (AllCreateClo (createClo :: CreateClo lτ dτ (m (val lτ dτ) lτ dτ)))
          (ltimeFilter :: TimeFilter)
          (dtimeFilter :: TimeFilter) -> f gc createClo ltimeFilter dtimeFilter

-- }}}
