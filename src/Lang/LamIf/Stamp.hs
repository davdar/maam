module Lang.LamIf.Stamp where

import FP
import Lang.LamIf.Syntax
import Lang.LamIf.Parser

data Name = Name
  { nameID ∷ ℕ
  , nameSource ∷ 𝕊
  }

instance Eq Name where (==) = (≟) `on` nameID
instance Ord Name where compare = compare `on` nameID
instance Pretty Name where pretty = ppBdr ∘ nameSource

data Exp = Exp
  { expID ∷ ℕ
  , expContext ∷ SourceContext Token
  , expRawExp ∷ PreExp Name Exp
  }
type Atom = PreAtom Name Exp

stripStampedPreExp ∷ PreExp Name Exp → PreExp 𝕊 (Fixed (PreExp 𝕊))
stripStampedPreExp = mapExp nameSource nameSource stripStampedExp

stripStampedExp ∷ Exp → Fixed (PreExp 𝕊)
stripStampedExp = Fixed ∘ stripStampedPreExp ∘ expRawExp

instance Eq Exp where (==) = (≟) `on` expID
instance Ord Exp where compare = (⋚) `on` expID
instance POrd Exp where (⊑⊒) = discretePO

instance Pretty Exp where
  pretty e = ppVertical
    -- [ ppHorizontal [ppHeader "ID:",pretty $ expID e]
    -- , ppHeader "Source:"
    [ pretty $ expContext e
    -- , ppHeader "AST:"
    -- , pretty $ stripStampedExp e
    ]

data StampState = StampState
  { stampNameID ∷ ℕ
  , stampExpID ∷ ℕ
  , stampBinderMap ∷ 𝕊 ⇰ ℕ
  }
makeLenses ''StampState

stampState₀ ∷ StampState
stampState₀ = StampState bot bot emptyDict

data StampEnv = StampEnv
  { stampContext ∷ SourceContext Token
  }
makeLenses ''StampEnv

stampEnv₀ ∷ StampEnv
stampEnv₀ = StampEnv null

newtype StampM a = StampM { runStampM ∷ ReaderT StampEnv (StateT StampState (Error Doc)) a }
  deriving 
    (Functor,Monad
    ,MonadError Doc
    ,MonadState StampState
    ,MonadReader StampEnv
    )

runStampM₀ ∷ StampM a → Doc ⨄ a
runStampM₀ xM = runError $ evalStateTWith stampState₀ $ runReaderTWith stampEnv₀ $ runStampM xM

stampExp ∷ SourceExp → StampM Exp
stampExp (SourceExp ctx e) = do
  i ← nextL stampExpIDL
  ei ← local (update stampContextL ctx) $ mapExpM stampVar stampBinder stampExp e
  return $ Exp i ctx ei

stampVar ∷ 𝕊 → StampM Name
stampVar x = do
  binderMap ← getL stampBinderMapL
  case binderMap # x of
    Nothing → do
      fc ← askL stampContextL
      throw $ ppVertical
        [ ppHeader "Bad Syntax: Unbound variable"
        , errorSourceContext fc
        ]
    Just n → return $ Name n x

stampBinder ∷ 𝕊 → StampM Name
stampBinder x = do
  i ← nextL stampNameIDL
  modifyL stampBinderMapL $ insertDict x i
  return $ Name i x

stamp ∷ SourceExp → Doc ⨄ Exp
stamp = runStampM₀ ∘ stampExp

-- ioError ∘ runStampM₀ ∘ stampExp *$ e_id
