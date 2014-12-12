module Lang.JS.Execution where

import FP
import MAAM
import Lang.JS.JS
import Lang.JS.Syntax

-- The type that is automatically generated as the state space functor from
-- (StateT Σ (ListSetT ID))
type MΣ' = ((ID :.: ListSet) :.: (,) Σ)

-- A nicer to look at state space functor that is isomorphic to MΣ'
newtype MΣ a = MΣ { unMΣ :: ListSet (a, Σ) }
  deriving (PartialOrder, JoinLattice)
instance Inject MΣ where inj = MΣ . inj . (,initial)
instance Morphism2 MΣ MΣ' where morph2 = Compose . Compose . ID . map swap . unMΣ
instance Morphism2 MΣ' MΣ where morph2 = MΣ . map swap . runID . runCompose . runCompose
instance Isomorphism2 MΣ MΣ'

-- A monad that satisfies the Analysis constraint
newtype M a = M { runM :: IsoMonadStep MΣ MΣ' (StateT Σ (ListSetT ID)) a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE Σ, MonadStateI Σ, MonadState Σ
    , MonadStep MΣ
    )
instance Analysis MΣ M

instance Initial Σ where
  initial = Σ ρ₀ σ₀ mapEmpty (KAddr 0) (Addr 0) (KAddr 0)
    where
      ρ₀ = fromList [(Name "$global", Addr 0)]
      σ₀ = fromList [(Addr 0, singleton $ ObjA $ Obj [])]

execM :: Exp -> ListSet (Exp, Σ)
execM = unMΣ . collectN (17::Int) (mstepγ evalM) . inj
  where
    evalM :: Exp -> M Exp
    evalM = eval
