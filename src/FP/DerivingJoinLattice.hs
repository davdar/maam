module FP.DerivingJoinLattice where

import FP.Core
import FP.TH
import Language.Haskell.TH

-- makeJoinLatticeLogic [C, D] ty [a, b] con [f1ty, f2ty] := [|
--   instance (JoinLattice f1ty, JoinLattice f2ty) => JoinLattice (ty a b) where
--     bot = con null null
--     con x1 x2 \/ con y1 y2 = con (x1 \/ y1) (x2 \/ y2)
-- |]
makeJoinLatticeLogic :: (Monad m, MonadQ m) => Cxt -> Name -> [TyVarBndr] -> Name -> [Type] -> m [Dec]
makeJoinLatticeLogic cx ty tyargs con fieldtys = do
  xs <- liftQ $ mapOnM fieldtys $ const $ newName $ toChars "x"
  ys <- liftQ $ mapOnM fieldtys $ const $ newName $ toChars "y"
  return $ single $
    InstanceD 
      (uniques $ concat [cx , map (ClassP ''JoinLattice . single) fieldtys])
      (ConT ''JoinLattice #@ (ConT ty #@| map (VarT . tyVarBndrName) tyargs))
      [ FunD 'bot $ single $ sclause [] $ 
          ConE con #@| (mapOn fieldtys $ const $ VarE 'bot)
      , FunD '(\/) $ single $ sclause [ConP con $ map VarP xs, ConP con $ map VarP ys] $
          ConE con #@| mapOn (unsafe_coerce justL $ zip xs ys) (uncurry $ \ x y -> VarE '(\/) #@ VarE x #@ VarE y)
      ]

makeJoinLattice :: Name -> Q [Dec]
makeJoinLattice name = do
  (cx, ty, tyargs, c, _) <- maybeZero . (coerceSingleConADT *. view tyConIL) *$ liftQ $ reify name
  (con, fieldtys) <- maybeZero $ coerceSimpleCon c
  makeJoinLatticeLogic cx ty tyargs con fieldtys

