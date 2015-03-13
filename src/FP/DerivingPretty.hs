module FP.DerivingPretty where

import FP.Core
import FP.TH
import FP.Pretty (Pretty(..))
import qualified FP.Pretty as P
import Language.Haskell.TH

-- makePrettySumLogic [C, D] ty [a, b] [(con1, [fieldty11, fieldty12]), (con2, [fieldty21, fieldty22])] := [|
--   instance (C, D, Pretty fieldty11, Pretty fieldty12, Pretty fieldty21, Pretty fieldty22) => Pretty (ty a b) where
--     pretty (con1 x1 x2) = app [con "con1", pretty x1, pretty x2]
--     pretty (con2 x1 x2) = app [con "con2", pretty x1, pretty x2]
-- |]
makePrettySumLogic :: (Monad m, MonadQ m) => Cxt -> Name -> [TyVarBndr] -> [(Name, [Type])] -> m [Dec]
makePrettySumLogic cx ty tyargs confieldtyss = do
  conxss <- liftQ $ mapOnM confieldtyss $ \ (con, fieldtys) -> do
    xs <- mapOnM fieldtys $ const $ newName $ toChars "x"
    return (con, xs)
  return $ single $
    InstanceD 
      (uniques $ concat [ cx , map (ClassP ''Pretty . single) $ concat $ map snd confieldtyss ])
      (ConT ''Pretty #@ (ConT ty #@| map (VarT . tyVarBndrName) tyargs)) $
      single $ FunD 'pretty $ mapOn conxss $ \ (con, xs) ->
        let prettyCon = VarE 'P.con #@ makeString (fromChars $ nameBase con)
            prettyXs = mapOn xs $ \ x -> VarE 'pretty #@ VarE x
        in 
        sclause [ConP con $ map VarP xs] $
          VarE 'P.app #@ prettyCon #@ makeList prettyXs

-- makePrettyUnionLogic [C, D] ty [a, b] [(con1, [fieldty11, fieldty12]), (con2, [fieldty21, fieldty22])] := [|
--   instance (C, D, Pretty fieldty11, Pretty fieldty12, Pretty fieldty21, Pretty fieldty2) => Pretty (ty a b) where
--     pretty (con1 x1 x2) = pretty (x1, x2)
--     pretty (con2 x1 x2) = pretty (x1, x2)
-- |]
makePrettyUnionLogic :: (Monad m, MonadQ m) => Cxt -> Name -> [TyVarBndr] -> [(Name, [Type])] -> m [Dec]
makePrettyUnionLogic cx ty tyargs confieldtyss = do
  conxss <- liftQ $ mapOnM confieldtyss $ \ (con, fieldtys) -> do
    xs <- mapOnM fieldtys $ const $ newName $ toChars "x"
    return (con, xs)
  return $ single $
    InstanceD
      (uniques $ concat [ cx , map (ClassP ''Pretty . single) $ concat $ map snd confieldtyss ])
      (ConT ''Pretty #@ (ConT ty #@| map (VarT . tyVarBndrName) tyargs)) $
      single $ FunD 'pretty $ mapOn conxss $ \ (con, xs) ->
        sclause [ConP con $ map VarP xs] $
          VarE 'pretty #@ tup (map VarE xs)

makePrettySum :: Name -> Q [Dec]
makePrettySum name = do
  (cx, ty, tyargs, cs, _) <- maybeZero . (coerceADT *. coerce tyConIL) *$ liftQ $ reify name
  scs <- mapM (maybeZero . coerceSimpleCon) cs
  makePrettySumLogic cx ty tyargs scs

makePrettyUnion :: Name -> Q [Dec]
makePrettyUnion name = do
  (cx, ty, tyargs, cs, _) <- maybeZero . (coerceADT *. coerce tyConIL) *$ liftQ $ reify name
  scs <- mapM (maybeZero . coerceSimpleCon) cs
  makePrettyUnionLogic cx ty tyargs scs
