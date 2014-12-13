module Lang.JS.StateSpace where

import FP
import Lang.JS.Syntax
import MAAM

newtype Addr  = Addr  Int deriving (Eq, Ord, PartialOrder, Peano, Pretty)
newtype KAddr = KAddr Int deriving (Eq, Ord, PartialOrder, Peano, Pretty)

type Env    = Map Name Addr
type Store  = Map Addr (Set AValue)
-- TODO: this should be Set (Maybe (Frame, KAddr))
type KStore = Map KAddr (Set (Frame, KAddr))

-- The type for the monadic state effect
data 𝒮 = 𝒮
  { env :: Env
  , store :: Store
  , kstore :: KStore
  , kon :: KAddr
  , nextAddr :: Addr
  , nextKAddr :: KAddr
  } deriving (Eq, Ord)

data Clo = Clo
  { arg :: [Name]
  , body :: TExp
  } deriving (Eq, Ord)

newtype Obj = Obj
  { fields :: [(String, (Set AValue))]
  } deriving (Eq, Ord)

data AValue =
    LitA Lit
  | NumA
  | StrA
  | BoolA
  | CloA Clo
  | ObjA Obj
    -- Fig 2. Mutable References
  | LocA Addr
  deriving (Eq, Ord)

data Frame = 
    LetK [(Name, Set AValue)] Name [(Name, TExp)] TExp
  | AppL [TExp]
  | AppR (Set AValue) [(Set AValue)] [TExp]
  | ObjK [(String, (Set AValue))] Name [(Name, TExp)]
    -- Array Dereferencing
  | FieldRefL TExp
  | FieldRefR (Set AValue)
    -- Array Assignment
  | FieldSetA TExp         TExp
  | FieldSetN (Set AValue) TExp
  | FieldSetV (Set AValue) (Set AValue)
    -- Property Deletion
  | DeleteL TExp
  | DeleteR (Set AValue)
    -- Fig 2. Mutable References
  | RefSetL TExp
  | RefSetR (Set AValue)
  | RefK
  | DeRefK
    -- Fig 8. Control Operators
  | IfK TExp TExp
  | SeqK TExp
  | WhileL TExp TExp
  | WhileR TExp TExp
  | LabelK Label
  | BreakK Label
  | TryCatchK TExp Name
  | TryFinallyL TExp
  | TryFinallyR (Set AValue)
  | ThrowK
    -- Fig 9. Primitive Operations
  | PrimOpK Op [(Set AValue)] [TExp]
  deriving (Eq, Ord)
instance PartialOrder Frame where pcompare = discreteOrder

class
  ( Monad m
  , MonadStateE 𝒮 m
  , MonadZero m
  , MonadPlus m
  , MonadStep ς m
  , JoinLattice (ς TExp)
  , Inject ς
  , PartialOrder (ς TExp)
  ) => Analysis ς m | m -> ς where

makeLenses ''𝒮
makePrettySum ''𝒮
makePrisms ''AValue
