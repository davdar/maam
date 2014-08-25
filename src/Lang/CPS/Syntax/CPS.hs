module Lang.CPS.Syntax.CPS where

import FP
import Lang.CPS.Syntax.AST
import qualified Lang.Direct.Syntax as D

fresh :: (MonadStateE Int m) => String -> m SName
fresh x = do
  i <- next
  return $ SName (Just i) x

lit :: D.Lit -> Lit
lit (D.I i) = I i
lit (D.B b) = B b

op :: D.Op -> Op
op D.Add1 = Add1
op D.Sub1 = Sub1
op D.IsNonNeg = IsNonNeg

data CPSKon r m a where
  MetaCPSKon :: (a -> m r) -> CPSKon r m a
  VarKon :: SName -> CPSKon r m SAtom
instance TransformerMorphism (CPSKon SCall) (K SCall) where
  ffmorph :: (Monad m) => CPSKon SCall m ~> K SCall m
  ffmorph (MetaCPSKon mk) = K mk
  ffmorph (VarKon k) = K $ \ a -> return $ Fix $ App (Var k) [a]
instance TransformerMorphism (K SCall) (CPSKon SCall) where
  ffmorph (K mk) = MetaCPSKon mk
instance TransformerIsomorphism (CPSKon SCall) (K SCall) where

reify :: (MonadStateE Int m) => CPSKon SCall m SAtom -> m SAtom
reify (MetaCPSKon mk) = do
  x <- fresh "x"
  c <- mk $ Var x
  return $ Lam [x] c
reify (VarKon k) = return $ Var k

reflect :: SName -> CPSKon SCall m SAtom
reflect = VarKon

-- {{{
-- letK :: (MonadStateE Int m, Monad m) => CPSKon SCall m SAtom -> (SName -> m SCall) -> m SCall
-- letK (VarKon k) mk = mk k
-- letK mk k = do
--   kx <- fresh "k"
--   c <- k kx
--   ok <- reify mk
--   return $ Fix $ App (Lam [kx] c) [ok]
-- }}}

letBind :: (MonadStateE Int m, MonadIsoKon CPSKon SCall m) => CPSKon SCall m SAtom -> m SName
letBind (VarKon k) = return k
letBind (MetaCPSKon mk) = do
  x <- fresh "x"
  c <- mk $ Var x
  let ok = Lam [x] c
  kx <- fresh "k"
  callMetaCC $ \ mk' -> do
    kc <- mk' kx 
    return $ Fix $ App (Lam [kx] kc) [ok]


-- {{{
-- letBindK :: (MonadStateE Int m, MonadIsoKon CPSKon SCall m) => m SAtom -> m SAtom
-- letBindK aM = callObjectCC $ \ ok -> letK ok $ \ rok -> withObjectC (reflect rok) aM
-- 
-- letBindK' :: (MonadStateE Int m, MonadIsoKon CPSKon SCall m) => m SAtom -> m SAtom
-- letBindK' aM = callObjectCC $ \ ok -> do
--   k <- letK' ok
--   withObjectC (reflect k) aM
-- }}}

cps :: (MonadIsoKon CPSKon SCall m, MonadStateE Int m) => D.Exp -> m SAtom
cps (D.Lit l) = return $ Lit $ lit l
cps (D.Var n) = return $ Var $ sname n
cps (D.Lam xs e) = do
  k <- fresh "k"
  Lam (map sname xs ++ [k]) <$> withObjectC (reflect k) $ cps e
cps (D.Prim o e) = Prim (op o) <$> cps e
cps (D.App f es) = do
  fa <- cps f
  eas <- mapM cps es
  callObjectCC $ \ ok -> do
    rok <- reify ok
    return $ Fix $ App fa (eas ++ [rok])
cps (D.If ce te fe) = do
  cae <- cps ce
  -- {{{
  --letBindK' $ callObjectCC $ \ ok ->
  --    unit (Fix .: If cae) <@> withObjectC ok (cps te) <@> withObjectC ok (cps fe)
  -- }}}
  callObjectCC $ \ ok -> do
    k <- letBind ok
    unit (Fix .: If cae) <@> withObjectC (reflect k) (cps te) <@> withObjectC (reflect k) (cps fe)

