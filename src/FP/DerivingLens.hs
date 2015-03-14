module FP.DerivingLens where

import FP.Core
import FP.TH
import Language.Haskell.TH

-- makeLensLogic [C, D] ty [a, b] field fieldty := [|
--   fieldL :: (C, D) => Lens (ty a b) fieldty
--   fieldL := lens field (\ x s -> s { field = x })
-- |]
makeLensLogic :: (Monad m, MonadQ m) => Cxt -> Name -> [TyVarBndr] -> Name -> Type -> m [Dec]
makeLensLogic cx ty tyargs field fieldty = do
  let lensName = mkName $ nameBase field ++ toChars "L"
  x <- liftQ $ newName $ toChars "x"
  s <- liftQ $ newName $ toChars "s"
  return
    [ SigD lensName $ 
        ForallT tyargs cx $
          ConT ''Lens #@ (ConT ty #@| map (VarT . tyVarBndrName) tyargs) #@ fieldty
    , FunD lensName
        [ sclause [] $ 
            VarE 'lens #@ VarE field #@ LamE [VarP s, VarP x] (RecUpdE (VarE s) [(field, VarE x)])
        ]
    ]

makeLenses :: Name -> Q [Dec]
makeLenses name = do
  (cx, ty, tyargs, c, _) <- maybeZero . (coerceSingleConADT *. view tyConIL) *$ liftQ $ reify name
  (_, fields) <- maybeZero $ view recCL c
  concat ^$ mapOnM fields $ \ (field, _, fieldty) -> do
    makeLensLogic cx ty tyargs field fieldty
