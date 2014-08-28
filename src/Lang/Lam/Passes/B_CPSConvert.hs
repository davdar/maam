module Lang.Lam.Passes.B_CPSConvert where

import FP
import Lang.Lam.CPS.Syntax
import Lang.Lam.Syntax (Exp, Name(..), GName(..), SGName, BdrNum(..), LocNum(..), SExp, sgNameFromSName)
import qualified Lang.Lam.Syntax as L
import qualified Lang.Lam.Passes.A_Stamp as Stamp

data St = St
  { callID :: LocNum
  , bdrID :: BdrNum
  , genID :: Int
  }
callIDL :: Lens St LocNum
callIDL = lens callID $ \ s i -> s { callID = i }
bdrIDL :: Lens St BdrNum
bdrIDL = lens bdrID $ \ s i -> s { bdrID = i }
genIDL :: Lens St Int
genIDL = lens genID $ \ s i -> s { genID = i }
stampL :: Lens St Stamp.St
stampL = lens lin lout
  where
    lin (St cid bid _) = Stamp.St cid bid
    lout (St _ _ gid) (Stamp.St cid bid) = St cid bid gid
-- stampInvL :: Lens Stamp.St St
-- stampInvL = lens lin lout
--   where
--     lin (Stamp.St eid bid) = St eid bid 0
--     lout _ (St cid bid _) = Stamp.St cid bid
st0 :: St
st0 = St pzero pzero pzero

type M m = (MonadStateE St m, MonadOpaqueKon CPSKon SGCall m)

fresh :: (M m) => String -> m SGName
fresh x = do
  i <- nextL bdrIDL
  g <- nextL genIDL
  return $ Stamped i $ GName (Just g) $ Name x

data CPSKon r m a where
  MetaCPSKon :: (a -> m r) -> CPSKon r m a
  AtomKon :: LocNum -> SGAtom -> CPSKon r m SGAtom
instance TransformerMorphism (CPSKon SGCall) (K SGCall) where
  ffmorph :: (Monad m) => CPSKon SGCall m ~> K SGCall m
  ffmorph (MetaCPSKon mk) = K mk
  ffmorph (AtomKon i k) = K $ return . StampedFix i . AppK k
instance TransformerMorphism (K SGCall) (CPSKon SGCall) where
  ffmorph (K mk) = MetaCPSKon mk

reify :: (M m) => CPSKon SGCall m SGAtom -> m SGAtom
reify (MetaCPSKon mk) = do
  x <- fresh "x"
  LamK x <$> mk $ Var $ x
reify (AtomKon _ a) = return a

reifyNamedAtom :: (M m) => LocNum -> SGAtom -> m SGName
reifyNamedAtom i k = do
  kx <- fresh "k"
  callMetaCC $ \ (mk' :: SGName -> m SGCall) -> do
    kc <- mk' kx
    return $ StampedFix i $ AppK (LamK kx kc) k

reifyNamed :: (M m) => CPSKon SGCall m SGAtom -> m SGName
reifyNamed (MetaCPSKon mk) = do
  x <- fresh "x"
  i <- nextL callIDL
  reifyNamedAtom i *$ LamK x <$> mk $ Var x
reifyNamed (AtomKon _ (Var k)) = return k
reifyNamed (AtomKon i k) = reifyNamedAtom i k

reflect :: (M m) => SGAtom -> m (CPSKon SGCall m SGAtom)
reflect a = do
  i <- nextL callIDL
  return $ AtomKon i a

cpsM :: (M m) => SExp -> m SGAtom
cpsM (StampedFix i e0) = case e0 of
  L.Lit l -> return $ Lit l
  L.Var n -> return $ Var $ sgNameFromSName n
  L.Lam x e -> do
    k <- fresh "k"
    rk <- reflect $ Var k
    LamF (sgNameFromSName x) k <$> withOpaqueC rk $ cpsM e
  L.Prim o e -> Prim o <$> cpsM e
  L.Let x e b -> do
    let sgx = sgNameFromSName x
    ea <- cpsM e
    callOpaqueCC $ \ (ok :: CPSKon SGCall m SGAtom) -> do
      bc <- withOpaqueC ok $ cpsM b
      return $ StampedFix i $ AppK (LamK sgx bc) ea
  L.App f e -> do
    fa <- cpsM f
    ea <- cpsM e
    callOpaqueCC $ \ ok -> do
      StampedFix i <$> AppF fa ea <$> reify ok
  L.If ce te fe -> do
    cae <- cpsM ce
    callOpaqueCC $ \ ok -> do
      k <- reifyNamed ok
      rk1 <- reflect $ Var k
      rk2 <- reflect $ Var k
      unit (StampedFix i .: If cae) <@> withOpaqueC rk1 (cpsM te) <@> withOpaqueC rk2 (cpsM fe)

newtype StStateT m a = StStateT { unStStateT :: StateT St m a }
  deriving
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadStateI St, MonadStateE St, MonadState St
    , MonadReaderI r, MonadReaderE r, MonadReader r
    )
instance (Monad m) => MonadStateE Stamp.St (StStateT m) where
  stateE :: StateT Stamp.St (StStateT m) ~> StStateT m
  stateE = stateE . stateLens stampL
-- instance (Monad m) => MonadStateI Stamp.St (StStateT m) where
--   stateI :: StStateT m ~> StateT Stamp.St (StStateT m)
--   stateI = stateLens stampInvL . stateI  
  
evalStStateT :: (Functor m) => St -> StStateT m a -> m a
evalStStateT s = evalStateT s . unStStateT

stampCPS :: Exp -> (SExp, SGCall)
stampCPS e = 
  -- let (se, Stamp.St eid bid) = runReader Stamp.env0 $ runStateT Stamp.st0 $ Stamp.stampM e
  --     c :: SGCall
  --     c = runMetaKon (evalStateT (St (psuc eid) bid 0) (cpsM se)) $ \ a -> StampedFix eid $ Halt a
  -- in (se, c)
     
  runReader Stamp.env0 $ evalStStateT st0 $ do
    se <- Stamp.stampM e
    c <- runMetaKonT (cpsM se) $ \ a -> do
      i' <- nextL callIDL
      return $ StampedFix i' $ Halt a
    return (se, c)

cps :: Exp -> SGCall
cps = snd . stampCPS
