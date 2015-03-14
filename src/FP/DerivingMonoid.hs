module FP.DerivingMonoid where

import FP.Core
import FP.TH
import Language.Haskell.TH

-- makeMonoidLogic [C, D] ty [a, b] con [f1ty, f2ty] := [|
--   instance (C, D, Monoid f1ty, Monoid f2ty) => Monoid (ty a b) where
--     null = con null null
--     con x1 x2 ++ con y1 y2 = con (x1 ++ y1) (x2 ++ y2)
-- |]
makeMonoidLogic :: (Monad m, MonadQ m) => Cxt -> Name -> [TyVarBndr] -> Name -> [Type] -> m [Dec]
makeMonoidLogic cx ty tyargs con fieldtys = do
  xys <- liftQ $ mapOnM fieldtys $ const $ newName (toChars "x") <*> newName (toChars "y")
  let xs = map fst xys
      ys = map snd xys
  return $ single $
    InstanceD 
      (uniques $ concat [cx , map (ClassP ''Monoid . single) fieldtys])
      (ConT ''Monoid #@ (ConT ty #@| map (VarT . tyVarBndrName) tyargs))
      [ FunD 'null $ single $ sclause [] $ 
          ConE con #@| (mapOn fieldtys $ const $ VarE 'null)
      , FunD '(++) $ single $ sclause [ConP con $ map VarP xs, ConP con $ map VarP ys] $
          ConE con #@| mapOn xys (uncurry $ \ x y -> VarE '(++) #@ VarE x #@ VarE y)
      ]

makeMonoid :: Name -> Q [Dec]
makeMonoid name = do
  (cx, ty, tyargs, c, _) <- maybeZero . (coerceSingleConADT *. view tyConIL) *$ liftQ $ reify name
  (con, fieldtys) <- maybeZero $ coerceSimpleCon c
  makeMonoidLogic cx ty tyargs con fieldtys
