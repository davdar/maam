module Lang.JS.Execution where

import FP
import MAAM
import Lang.JS.JS
import Lang.JS.Syntax

type FIguts = StateT Σ (ListSetT ID)
type SS' = ((ID :.: ListSet) :.: (,) Σ)
newtype SS a = SS { unSS :: ListSet (a, Σ) }
  deriving (PartialOrder, JoinLattice)
instance Inject SS where
  inj = SS . inj . (,initial)
instance Morphism2 SS SS' where
  morph2 = Compose . Compose . ID . map swap . unSS
instance Morphism2 SS' SS where
  morph2 = SS . map swap . runID . runCompose . runCompose
instance Isomorphism2 SS SS' where
newtype FI a = FI { runFI :: IsoMonadStep SS SS' FIguts a }
  deriving 
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadZero, MonadPlus
    , MonadStateE Σ, MonadStateI Σ, MonadState Σ
    , MonadStep SS
    )
instance Analysis SS FI where

newtype SSS a = SSS { unSSS :: Set (a, Σ) }
  deriving (PartialOrder, JoinLattice)
instance (Ord a) => Morphism (SS a) (SSS a) where
  morph = SSS . fromList . toList . unSS
instance (Ord a) => Morphism (SSS a) (SS a) where
  morph = SS . fromList . toList . unSSS
instance (Ord a) => Isomorphism (SS a) (SSS a) where

execCollect :: (Analysis ς m, PartialOrder ς', JoinLattice ς') => (Exp -> m Exp) -> (ς Exp -> ς') -> (ς' -> ς Exp) -> Exp -> ς'
execCollect step to from = collect (to . mstepγ step . from) . to . inj

execCollectFI :: Exp -> Set (Exp, Σ)
execCollectFI = unSSS . collect (isoto . mstepγ (eval :: Exp -> FI Exp) . isofrom) . isoto . (inj :: Exp -> SS Exp)
