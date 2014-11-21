module Lang.Lam.CPS.Instances.Val where

import FP
import Lang.Lam.CPS.Classes.Val
import qualified FP.Pretty as P
import Lang.Lam.Syntax (Lit(..), iL, bL, Op(..))

-- Concrete {{{

data CVal lτ dτ = LitC Lit | CloC (Clo lτ dτ)
  deriving (Eq, Ord)
instance (Pretty lτ, Pretty dτ) => Pretty (CVal lτ dτ) where
  pretty (LitC l) = pretty l
  pretty (CloC c) = pretty c

litCL :: Prism (CVal lτ dτ) Lit
litCL = Prism
  { coerce = \ v -> case v of
      LitC l -> Just l
      _ -> Nothing
  , inject = LitC
  }
cloCL :: Prism (CVal lτ dτ) (Clo lτ dτ)
cloCL = Prism
  { coerce = \ v -> case v of
      CloC c -> Just c
      _ -> Nothing
  , inject = CloC
  }

newtype PCVal lτ dτ = PCVal { runPCVal :: Set (CVal lτ dτ) }
  deriving (Eq, Ord, JoinLattice, Pretty)

pcvalL :: Lens (PCVal lτ dτ) (Set (CVal lτ dτ))
pcvalL = isoLens runPCVal PCVal

instance Val PCVal where
  lit :: (Ord lτ, Ord dτ) => Lit -> PCVal lτ dτ
  lit = PCVal . singleton . LitC
  clo :: (Ord lτ, Ord dτ) => Clo lτ dτ -> PCVal lτ dτ
  clo = PCVal . singleton . CloC
  op :: (Ord lτ, Ord dτ) => Op -> PCVal lτ dτ -> PCVal lτ dτ
  op Add1     = update pcvalL $ setMap (LitC . I) . extend (setMap (+1)    . maybeSet . coerce (iL <.> litCL))
  op Sub1     = update pcvalL $ setMap (LitC . I) . extend (setMap (+(-1)) . maybeSet . coerce (iL <.> litCL))
  op IsNonNeg = update pcvalL $ setMap (LitC . B) . extend (setMap (>=0)   . maybeSet . coerce (iL <.> litCL))
  elimBool :: (Ord lτ, Ord dτ) => PCVal lτ dτ -> Set Bool
  elimBool = extend (maybeSet . coerce (bL <.> litCL)) . runPCVal
  elimClo :: (Ord lτ, Ord dτ) => PCVal lτ dτ -> Set (Clo lτ dτ)
  elimClo = extend (maybeSet . coerce cloCL) . runPCVal

-- }}}

-- Abstract {{{

data AVal lτ dτ = LitA Lit | IA | CloA (Clo lτ dτ)
  deriving (Eq, Ord)
instance (Pretty lτ, Pretty dτ) => Pretty (AVal lτ dτ) where
  pretty (LitA l) = pretty l
  pretty IA = P.lit "INT"
  pretty (CloA c) = pretty c

litAL :: Prism (AVal lτ dτ) Lit
litAL = Prism
  { coerce = \ v -> case v of
      LitA l -> Just l
      _ -> Nothing
  , inject = LitA
  }

iAL :: Prism (AVal lτ dτ) ()
iAL = Prism
  { coerce = \ v -> case v of
      IA -> Just ()
      _ -> Nothing
  , inject = \ () -> IA
  }

isIntA :: AVal lτ dτ -> Bool
isIntA = isL iAL \/ isL litAL

cloAL :: Prism (AVal lτ dτ) (Clo lτ dτ)
cloAL = Prism
  { coerce = \ v -> case v of
      CloA c -> Just c
      _ -> Nothing
  , inject = CloA
  }

newtype PAVal lτ dτ = PAVal { runPAVal :: Set (AVal lτ dτ) }
  deriving (Eq, Ord, PartialOrder, JoinLattice, Pretty)

pavalL :: Lens (PAVal lτ dτ) (Set (AVal lτ dτ))
pavalL = isoLens runPAVal PAVal

instance Val PAVal where
  lit :: (Ord lτ, Ord dτ) => Lit -> PAVal lτ dτ
  lit (I i) = PAVal $ singleton $ LitA $ I i
  lit (B b) = PAVal $ singleton $ LitA $ B b
  clo :: (Ord lτ, Ord dτ) => Clo lτ dτ -> PAVal lτ dτ
  clo = PAVal . singleton . CloA
  op :: (Ord lτ, Ord dτ) => Op -> PAVal lτ dτ -> PAVal lτ dτ
  op Add1     = update pavalL $ setMap (const IA) . extend (maybeSet . (coerce iAL ++ (void . coerce (iL <.> litAL))))
  op Sub1     = update pavalL $ setMap (const IA) . extend (maybeSet . (coerce iAL ++ (void . coerce (iL <.> litAL))))
  op IsNonNeg = update pavalL $ extend $ joins
    [ setMap (LitA . B . (>=0)) . maybeSet . coerce (iL <.> litAL)
    , setMap (LitA . B) . extend (const $ toSet [True, False]) . maybeSet . coerce iAL
    ]
  elimBool :: (Ord lτ, Ord dτ) => PAVal lτ dτ -> Set Bool
  elimBool = extend (maybeSet . coerce (bL <.> litAL)) . runPAVal
  elimClo :: (Ord lτ, Ord dτ) => PAVal lτ dτ -> Set (Clo lτ dτ)
  elimClo = extend (maybeSet . coerce cloAL) . runPAVal

-- }}}
