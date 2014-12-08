module Lang.CPS.Val where

import FP
import Lang.Common
import Lang.CPS.Syntax
import MAAM
import qualified FP.Pretty as P

newtype Lτ lτ ψ = Lτ { getlτ :: lτ ψ }
  deriving (Eq, Ord, Pretty, Initial)
makeLenses ''Lτ
newtype Dτ dτ ψ = Dτ { getdτ :: dτ ψ }
  deriving (Eq, Ord, Pretty, Initial)
makeLenses ''Dτ

data Addr lτ dτ (ψ :: *) = Addr
  { addrLocation :: SGName
  , addrLexicalTime :: Lτ lτ ψ
  , addrDynamicTime :: Dτ dτ ψ
  } deriving (Eq, Ord)
instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (Addr lτ dτ ψ) where
  pretty (Addr loc lτ dτ) = P.collection "<" ">" "," 
    [ exec [P.pun "x=", P.align $ pretty loc]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    , exec [P.pun "dτ=", P.align $ pretty dτ]
    ]

newtype Env lτ dτ ψ = Env { runEnv :: Map SGName (Addr lτ dτ ψ) }
  deriving (Eq, Ord, Pretty)
makeLenses ''Env
instance Initial (Env lτ dτ ψ) where initial = Env mapEmpty

newtype Store val lτ dτ ψ = Store { runStore :: Map (Addr lτ dτ ψ) (val lτ dτ ψ) }
  deriving (Eq, Ord, PartialOrder, JoinLattice, Pretty)
makeLenses ''Store
instance Initial (Store val lτ dτ ψ) where initial = Store mapEmpty

data Clo lτ dτ ψ = Clo 
  { cloLoc :: LocNum
  , cloArgs :: [SGName]
  , cloCall :: SGCall
  , cloEnv :: Env lτ dτ ψ
  , cloTime :: Lτ lτ ψ
  } deriving (Eq, Ord)
instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (Clo lτ dτ ψ) where
  pretty (Clo l _xs _c _ρ lτ) = P.collection "<" ">" "," 
    [ exec [P.pun "λ=", pretty l]
    , exec [P.pun "lτ=", P.align $ pretty lτ]
    ]

class Val val where
  lit :: (Ord (lτ ψ), Ord (dτ ψ)) => Lit -> val lτ dτ ψ
  clo :: (Ord (lτ ψ), Ord (dτ ψ)) => Clo lτ dτ ψ -> val lτ dτ ψ
  op :: (Ord (lτ ψ), Ord (dτ ψ)) => Op -> val lτ dτ ψ -> val lτ dτ ψ
  elimBool :: (Ord (lτ ψ), Ord (dτ ψ)) => val lτ dτ ψ -> Set Bool
  elimClo :: (Ord (lτ ψ), Ord (dτ ψ)) => val lτ dτ ψ -> Set (Clo lτ dτ ψ)

-- Concrete
data CVal lτ dτ ψ = LitC Lit | CloC (Clo lτ dτ ψ)
  deriving (Eq, Ord)
makePrisms ''CVal
instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (CVal lτ dτ ψ) where
  pretty (LitC l) = pretty l
  pretty (CloC c) = pretty c

newtype PCVal lτ dτ ψ = PCVal { runPCVal :: Set (CVal lτ dτ ψ) }
  deriving (Eq, Ord, PartialOrder, JoinLattice, Pretty)
makeLenses ''PCVal

instance Val PCVal where
  lit :: (Ord (lτ ψ), Ord (dτ ψ)) => Lit -> PCVal lτ dτ ψ
  lit = PCVal . singleton . LitC
  clo :: (Ord (lτ ψ), Ord (dτ ψ)) => Clo lτ dτ ψ -> PCVal lτ dτ ψ
  clo = PCVal . singleton . CloC
  op :: (Ord (lτ ψ), Ord (dτ ψ)) => Op -> PCVal lτ dτ ψ -> PCVal lτ dτ ψ
  op Add1     = update runPCValL $ setMap (LitC . I) . extend (setMap (+1)    . liftMaybeSet . coerce (iL <.> litCL))
  op Sub1     = update runPCValL $ setMap (LitC . I) . extend (setMap (+(-1)) . liftMaybeSet . coerce (iL <.> litCL))
  op IsNonNeg = update runPCValL $ setMap (LitC . B) . extend (setMap (>=0)   . liftMaybeSet . coerce (iL <.> litCL))
  elimBool :: (Ord (lτ ψ), Ord (dτ ψ)) => PCVal lτ dτ ψ -> Set Bool
  elimBool = extend (liftMaybeSet . coerce (bL <.> litCL)) . runPCVal
  elimClo :: (Ord (lτ ψ), Ord (dτ ψ)) => PCVal lτ dτ ψ -> Set (Clo lτ dτ ψ)
  elimClo = extend (liftMaybeSet . coerce cloCL) . runPCVal

-- Abstract
data AVal lτ dτ ψ = LitA Lit | IA | CloA (Clo lτ dτ ψ)
  deriving (Eq, Ord)
makePrisms ''AVal
instance (Pretty (lτ ψ), Pretty (dτ ψ)) => Pretty (AVal lτ dτ ψ) where
  pretty (LitA l) = pretty l
  pretty IA = P.lit "INT"
  pretty (CloA c) = pretty c

isIntA :: AVal lτ dτ ψ -> Bool
isIntA = isL iAL \/ isL litAL

newtype PAVal lτ dτ ψ = PAVal { runPAVal :: Set (AVal lτ dτ ψ) }
  deriving (Eq, Ord, PartialOrder, JoinLattice, Pretty)
makeLenses ''PAVal

instance Val PAVal where
  lit :: (Ord (lτ ψ), Ord (dτ ψ)) => Lit -> PAVal lτ dτ ψ
  lit (I i) = PAVal $ singleton $ LitA $ I i
  lit (B b) = PAVal $ singleton $ LitA $ B b
  clo :: (Ord (lτ ψ), Ord (dτ ψ)) => Clo lτ dτ ψ -> PAVal lτ dτ ψ
  clo = PAVal . singleton . CloA
  op :: (Ord (lτ ψ), Ord (dτ ψ)) => Op -> PAVal lτ dτ ψ -> PAVal lτ dτ ψ
  op Add1     = update runPAValL $ setMap (const IA) . extend (liftMaybeSet . (coerce iAL ++ (void . coerce (iL <.> litAL))))
  op Sub1     = update runPAValL $ setMap (const IA) . extend (liftMaybeSet . (coerce iAL ++ (void . coerce (iL <.> litAL))))
  op IsNonNeg = update runPAValL $ extend $ joins
    [ setMap (LitA . B . (>=0)) . liftMaybeSet . coerce (iL <.> litAL)
    , setMap (LitA . B) . extend (const $ toSet [True, False]) . liftMaybeSet . coerce iAL
    ]
  elimBool :: (Ord (lτ ψ), Ord (dτ ψ)) => PAVal lτ dτ ψ -> Set Bool
  elimBool = extend (liftMaybeSet . coerce (bL <.> litAL)) . runPAVal
  elimClo :: (Ord (lτ ψ), Ord (dτ ψ)) => PAVal lτ dτ ψ -> Set (Clo lτ dτ ψ)
  elimClo = extend (liftMaybeSet . coerce cloAL) . runPAVal
