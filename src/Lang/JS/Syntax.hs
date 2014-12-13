module Lang.JS.Syntax
  ( module Lang.JS.Syntax
  , module Lang.Common
  , module Language.LambdaJS.Syntax
  ) where

import FP
import qualified FP.Pretty as P
import Language.LambdaJS.Syntax (Op(..), Label, SourcePos)
import Lang.Common (Name(..), VarLam(..))

newtype Stamp = Stamp { unStamp :: Int }
  deriving (Eq, Ord, Peano, FromInteger)
instance Pretty Stamp where pretty = P.pun . ptoString . unStamp

data Lit = B Bool | UndefinedL | NullL | S String | N Double
  deriving (Eq, Ord)
makePrisms ''Lit
instance PartialOrder Lit where pcompare = discreteOrder

data PreExp e =
    Lit Lit
  | Var Name
  | Func [Name] e
  | ObjE [(Name, e)]
  -- | Prim Op e
  | Let [(Name, e)] e
  | App e [e]
  | FieldRef e e
  | FieldSet e e e
  | Delete e e
    -- Fig 2. Mutable References
  | RefSet e e
  | Ref e
  | DeRef e
    -- Fig 8. Control Operators
  | If e e e
  | Seq e e
  | While e e
  | LabelE Label e
  | Break Label e
  | TryCatch e Name e
  | TryFinally e e
  | Throw e
    -- Fig 9. Primitive Operators
  | PrimOp Op [e]
  deriving (Eq, Ord)
instance FunctorM PreExp where
  mapM :: (Monad m) => (a -> m b) -> PreExp a -> m (PreExp b)
  mapM f = \ case
    Lit l -> return $ Lit l
    Var x -> return $ Var x
    Func xs e -> Func xs ^@ f e
    ObjE xes -> ObjE ^@ mapM (\ (x, e') -> (x,) ^@ f e') xes
    Let xes e -> Let ^@ mapM (\ (x, e') -> (x,) ^@ f e') xes <@> f e
    App e es -> App ^@ f e <@> mapM f es
    FieldRef e₁ e₂ -> FieldRef ^@ f e₁ <@> f e₂
    FieldSet e₁ e₂ e₃ -> FieldSet ^@ f e₁ <@> f e₂ <@> f e₃
    Delete e₁ e₂ -> Delete ^@ f e₁ <@> f e₂
    RefSet e₁ e₂ -> RefSet ^@ f e₁ <@> f e₂
    Ref e -> Ref ^@ f e
    DeRef e -> DeRef ^@ f e
    If e₁ e₂ e₃ -> If ^@ f e₁ <@> f e₂ <@> f e₃
    Seq e₁ e₂ -> Seq ^@ f e₁ <@> f e₂
    While e₁ e₂ -> While ^@ f e₁ <@> f e₂
    LabelE l e -> LabelE l ^@ f e
    Break l e -> Break l ^@ f e
    TryCatch e₁ x e₂ -> TryCatch ^@ f e₁ <@> return x <@> f e₂
    TryFinally e₁ e₂ -> TryFinally ^@ f e₁ <@> f e₂
    Throw e -> Throw ^@ f e
    PrimOp o es -> PrimOp o ^@ mapM f es

instance Functor PreExp where 
  map f = runID . mapM (kleisli f)

type Exp = Fix PreExp
type TExp = StampedFix Stamp PreExp
type PreTExp = PreExp TExp

stampM :: Exp -> State Stamp TExp
stampM (Fix e) = do
  t <- next
  e' <- mapM stampM e
  return $ StampedFix t e'

stamp :: Exp -> TExp
stamp = evalState 0 . stampM
