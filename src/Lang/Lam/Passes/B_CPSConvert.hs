module Lang.Lam.Passes.B_CPSConvert where

import FP
import Lang.Lam.CPS.Syntax
import Lang.Lam.Syntax (Name(..), GName(..), SGName, StampedExp)
import qualified Lang.Lam.Syntax as L

data St = St
  { callID :: Int
  , bdrID :: Int
  , genID :: Int
  }
callIDL :: Lens St Int
callIDL = lens callID $ \ s i -> s { callID = i }
bdrIDL :: Lens St Int
bdrIDL = lens bdrID $ \ s i -> s { bdrID = i }
genIDL :: Lens St Int
genIDL = lens genID $ \ s i -> s { genID = i }
st0 :: St
st0 = St 0 0 0

type M m = (MonadStateE St m, MonadIsoKon CPSKon (Call SGName) m)

fresh :: (M m) => String -> m SGName
fresh x = do
  i <- nextL callIDL
  g <- nextL genIDL
  return $ Stamped i $ GName (Just g) $ Name x

data CPSKon r m a where
  MetaCPSKon :: (a -> m r) -> CPSKon r m a
  VarKon :: Int -> SGName -> CPSKon r m (Atom SGName)
instance TransformerMorphism (CPSKon (Call SGName)) (K (Call SGName)) where
  ffmorph :: (Monad m) => CPSKon (Call SGName) m ~> K (Call SGName) m
  ffmorph (MetaCPSKon mk) = K mk
  ffmorph (VarKon i k) = K $ \ a -> do
    return $ StampedFix i $ AppK (Var k) a
instance TransformerMorphism (K (Call SGName)) (CPSKon (Call SGName)) where
  ffmorph (K mk) = MetaCPSKon mk
instance TransformerIsomorphism (CPSKon (Call SGName)) (K (Call SGName)) where

reify :: (M m) => CPSKon (Call SGName) m (Atom SGName) -> m (Atom SGName)
reify (MetaCPSKon mk) = do
  x <- fresh "x"
  c <- mk $ Var $ x
  return $ LamK x c
reify (VarKon _ k) = return $ Var k

reflect :: (M m) => SGName -> m (CPSKon (Call SGName) m (Atom SGName))
reflect n = unit VarKon <@> nextL callIDL <@> unit n

reifyNamed :: (M m) => CPSKon (Call SGName) m (Atom SGName) -> m SGName
reifyNamed (VarKon _ k) = return k
reifyNamed (MetaCPSKon mk) = do
  x <- fresh "x"
  c <- mk $ Var x
  let ok = LamK x c
  kx <- fresh "k"
  callMetaCC $ \ mk' -> do
    kc <- mk' kx 
    i <- nextL callIDL
    return $ StampedFix i $ AppK (LamK kx kc) ok

cps :: (M m) => StampedExp SGName -> m (Atom SGName)
cps (StampedFix i e0) = case e0 of
  L.Lit l -> return $ Lit l
  L.Var n -> return $ Var n
  L.Lam x e -> do
    k <- fresh "k"
    rk <- reflect k
    LamF x k <$> withOpaqueC rk $ cps e
  L.Prim o e -> Prim o <$> cps e
  L.App f e -> do
    fa <- cps f
    ea <- cps e
    callOpaqueCC $ \ ok -> do
      rok <- reify ok
      return $ StampedFix i $ AppF fa ea rok
  L.If ce te fe -> do
    cae <- cps ce
    callOpaqueCC $ \ ok -> do
      k <- reifyNamed ok
      rk1 <- reflect k
      rk2 <- reflect k
      unit (StampedFix i .: If cae) <@> withOpaqueC rk1 (cps te) <@> withOpaqueC rk2 (cps fe)
