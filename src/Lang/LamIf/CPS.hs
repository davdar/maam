module Lang.LamIf.CPS where

import FP
import Lang.LamIf.Syntax hiding (PreExp(..))

data PrePico n =
    Lit Lit
  | Var n
  deriving (Eq, Ord)
type Pico = PrePico Name

data PreAtom n c =
    Pico (PrePico n)
  | Prim LBinOp (PrePico n) (PrePico n)
  | LamF n n c
  | LamK n c
  | Tup (PrePico n) (PrePico n)
  | Pi1 (PrePico n)
  | Pi2 (PrePico n)
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (PreAtom n c) where pcompare = discreteOrder
type Atom = Stamped LocNum (PreAtom Name Call)

data PreCall n c =
    Let n (Stamped LocNum (PreAtom n c)) c
  | If (PrePico n) c c 
  | AppF (PrePico n) (PrePico n) (PrePico n)
  | AppK (PrePico n) (PrePico n)
  | Halt (PrePico n)
  deriving (Eq, Ord)
instance (Eq n, Eq c) => PartialOrder (PreCall n c) where pcompare = discreteOrder
type Call = StampedFix LocNum (PreCall Name)
makePrisms ''PreCall

freeVarsLam :: Set Name -> [Name] -> Call -> Set Name
freeVarsLam ρ xs c = freeVarsCall (ρ \/ toSet xs) c

freeVarsPico :: Set Name -> Pico -> Set Name
freeVarsPico _ (Lit _) = bot
freeVarsPico ρ (Var x) 
  | ρ ? x = bot
  | otherwise = single x

freeVarsAtom :: Set Name -> Atom -> Set Name
freeVarsAtom ρ a = case stamped a of
  Pico p -> freeVarsPico ρ p
  Prim _ a1 a2 -> freeVarsPico ρ a1 \/ freeVarsPico ρ a2
  LamF x kx c -> freeVarsLam ρ [x, kx] c
  LamK x c -> freeVarsLam ρ [x] c
  Tup p1 p2 -> freeVarsPico ρ p1 \/ freeVarsPico ρ p2
  Pi1 p -> freeVarsPico ρ p
  Pi2 p -> freeVarsPico ρ p

freeVarsCall :: Set Name -> Call -> Set Name
freeVarsCall ρ c = case stampedFix c of
  Let x a c' -> joins [ freeVarsAtom ρ a, freeVarsCall (insert x ρ) c' ]
  If ax tc fc -> joins [ freeVarsPico ρ ax, freeVarsCall ρ tc, freeVarsCall ρ fc ]
  AppF fx ax kx -> joins $ freeVarsPico ρ ^$ [fx, ax, kx]
  AppK kx ax -> joins $ freeVarsPico ρ ^$ [kx, ax]
  Halt ax -> freeVarsPico ρ ax
