module Lang.LamIf.Semantics where

import FP
import MAAM
import Lang.LamIf.Values
import Lang.LamIf.Stamp
import Lang.LamIf.Syntax
import Lang.LamIf.Time

data LamIfState val = LamIfState
  { env ∷ Env
  , κAddr ∷ Maybe ExpAddr
  , time ∷ Time
  , store ∷ Store val
  , κStore ∷ KStore val
  }
  deriving (Eq,Ord)
makeLenses ''LamIfState
makePrettyRecord ''LamIfState
instance (POrd val) ⇒ POrd (LamIfState val) where
  (⊑⊒) = poCompareFromLte $ \ (LamIfState ρ₁ κl₁ τ₁ σ₁ κσ₁) (LamIfState ρ₂ κl₂ τ₂ σ₂ κσ₂) → 
    meets [ρ₁ ⊑ ρ₂,κl₁ ⊑ κl₂,τ₁ ⊑ τ₂,σ₁ ⊑ σ₂,κσ₁ ⊑ κσ₂]

data LamIfEnv = LamIfEnv
  { currentExp ∷ Exp
  , timeParam ∷ TimeParam
  }
makeLenses ''LamIfEnv

class 
  ( POrd val
  , JoinLattice val
  , Val val
  , Monad m
  , MonadState (LamIfState val) m
  , MonadJoinLattice m
  ) ⇒ MonadLamIf val m | m → val

type ParamsM m = ReaderT LamIfEnv m

atom ∷ (MonadLamIf val m) ⇒ Atom → ParamsM m AtomVal
atom (AInteger i) = return $ AtomValInt i
atom (AVar x) = do
  ρ ← getL envL
  case ρ # x of
    Nothing → mbot
    Just l → return $ AtomValAddr l
atom (ALam x e) = do
  ρ ← getL envL
  ce ← askL currentExpL
  τ ← getL (lexicalL ⌾ timeL)
  return $ AtomValClo $ Closure ce x e ρ τ

atomVal ∷ (MonadLamIf val m) ⇒ AtomVal → ParamsM m val
atomVal (AtomValInt i) = return $ intI i
atomVal (AtomValAddr l) = do
  σ ← getL storeL
  case σ # l of
    Nothing → mbot
    Just v → return v
atomVal (AtomValClo clo) = return $ cloI clo
atomVal (AtomValOp o av₁ av₂) = do
  v₁ ← atomVal av₁
  v₂ ← atomVal av₂
  return $ δ o v₁ v₂

push ∷ (MonadLamIf val m) ⇒ Frame → ParamsM m ()
push fr = do
  τ ← getL timeL
  e ← askL currentExpL
  let κl = Just $ ExpAddr e τ
  κl' ← getL κAddrL
  modifyL κStoreL $ \ κσ → κσ ⊔ dict [κl ↦ frameI (fr,κl')]
  putL κAddrL κl

pop ∷ (MonadLamIf val m) ⇒ ParamsM m Frame
pop = do
  κl ← getL κAddrL
  κσ ← getL κStoreL
  case κσ # κl of
    Nothing → mbot
    Just v → do
      (fr,κl') ← mset $ frameE v
      putL κAddrL κl'
      return fr

bind ∷ (MonadLamIf val m) ⇒ Name → val → ParamsM m ()
bind x v = do
  τ ← getL timeL
  let l = VarAddr x τ
  modifyL envL $ \ ρ → insertDict x l ρ 
  modifyL storeL $ \ σ → σ ⊔ dict [l ↦ v]

tickL ∷ (MonadLamIf val m) ⇒ Exp → (Lens LamIfEnv (Maybe ℕ)) → (Lens (LamIfState val) [Exp]) → ParamsM m ()
tickL ce kL τL = do
  k ← askL kL
  modifyL τL $ \ τ → elimMaybe id firstN k $ ce:τ

tickO ∷ (MonadLamIf val m) ⇒ Exp → ParamsM m ()
tickO ce = do
  tickL ce (lexicalObjDepthL ⌾ timeParamL) (objL ⌾ lexicalL ⌾ timeL)
  tickL ce (dynamicObjDepthL ⌾ timeParamL) (objL ⌾ dynamicL ⌾ timeL)

refine ∷ (MonadLamIf val m) ⇒ Name → val → ParamsM m ()
refine x v = do
  ρ ← getL envL
  σ ← getL storeL
  case ρ # x of
    Nothing → mbot
    Just l → putL storeL $ insertDict l v σ

delZeroM ∷ (MonadLamIf val m) ⇒ Name → ParamsM m ()
delZeroM x = do
  ρ ← getL envL
  case ρ # x of
    Nothing → mbot
    Just l → modifyL storeL $ modifyDict delZero l

stackReturn ∷ (MonadLamIf val m) ⇒ Maybe Atom → AtomVal → ParamsM m Exp
stackReturn aM v = do
  fr ← pop
  case fr of
    IfH e₂ e₃ ρ lτ → do
      putL envL ρ
      putL (lexicalL ⌾ timeL) lτ
      b ← mset ∘ isZeroE *$ atomVal v
      when b $
        whenMaybe (view (aVarL ⌾ justL) aM) $ \ x → refine x $ intI $ 𝕫 0
      when (not b) $
        whenMaybe (view (aVarL ⌾ justL) aM) $ \ x → delZeroM x
      return $ if b then e₂ else e₃
    LetH x e₂ ρ lτ → do
      putL envL ρ
      putL (lexicalL ⌾ timeL) lτ
      bind x *$ atomVal v
      return e₂
    OpL o e₂ ρ lτ → do
      putL envL ρ
      putL (lexicalL ⌾ timeL) lτ
      push $ OpR v o
      return e₂
    OpR v₁ o → do
      stackReturn Nothing $ AtomValOp o v₁ v
    AppL e₂ ρ lτ → do
      putL envL ρ
      putL (lexicalL ⌾ timeL) lτ
      push $ AppR v
      return e₂
    AppR v₁ → do
      Closure ce x e ρ lτ ← mset ∘ cloE *$ atomVal v₁
      putL envL ρ
      putL (lexicalL ⌾ timeL) lτ
      tickO ce
      bind x *$ atomVal v
      return e

tickK ∷ (MonadLamIf val m) ⇒ ParamsM m ()
tickK = do
  ce ← askL currentExpL
  tickL ce (lexicalCallDepthL ⌾ timeParamL) (callL ⌾ lexicalL ⌾ timeL)
  tickL ce (dynamicCallDepthL ⌾ timeParamL)  (callL ⌾ dynamicL ⌾ timeL)

step ∷ (MonadLamIf val m) ⇒ TimeParam → Exp → m Exp
step ps e = runReaderTWith (LamIfEnv e ps) $ do
  tickK
  case expRawExp e of
    EAtom a → do
      v ← atom a
      stackReturn (Just a) v
    EIf e₁ e₂ e₃ → do
      ρ ← getL envL
      lτ ← getL (lexicalL ⌾ timeL)
      push $ IfH e₂ e₃ ρ lτ
      return e₁
    ELet x e₁ e₂ → do
      ρ ← getL envL
      lτ ← getL (lexicalL ⌾ timeL)
      push $ LetH x e₂ ρ lτ
      return e₁
    EOp o e₁ e₂ → do
      ρ ← getL envL
      lτ ← getL (lexicalL ⌾ timeL)
      push $ OpL o e₂ ρ lτ
      return e₁
    EApp e₁ e₂ → do
      ρ ← getL envL
      lτ ← getL (lexicalL ⌾ timeL)
      push $ AppL e₂ ρ lτ
      return e₁

gc ∷ (MonadLamIf val m) ⇒ Exp → m ()
gc = undefined

class 
  ( MonadLamIf val m
  , Inject ι ς
  , GaloisTransformer ς m
  ) ⇒ ExecutionLamIf val ι ς m | m → val,m → ς

type LFPLamIf ς = (POrd (ς Exp),JoinLattice (ς Exp),Difference (ς Exp))

ex ∷ (ExecutionLamIf val ι ς' m,LFPLamIf ς) ⇒ TimeParam → ς Exp ⇄ ς' Exp → (Exp → m Exp) → ς Exp → ς Exp
ex ps iso f = collect (isoFrom iso ∘ γGT (f *∘ step ps) ∘ isoTo iso)

exDiffs ∷ (ExecutionLamIf val ι ς' m,LFPLamIf ς) ⇒ TimeParam → ς Exp ⇄ ς' Exp → (Exp → m Exp) → ς Exp → Stream (ς Exp)
exDiffs ps iso f = collectDiffs (isoFrom iso ∘ γGT (f *∘ step ps) ∘ isoTo iso)
