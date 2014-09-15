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
st0 :: St
st0 = St pzero pzero pzero

type M m = (MonadOpaqueKon CPSKon SGCall m, MonadState St m)

fresh :: (M m) => String -> m SGName
fresh x = do
  i <- nextL bdrIDL
  g <- nextL genIDL
  return $ Stamped i $ GName (Just g) $ Name x

data CPSKon r m a where
  MetaKon :: (a -> m r) -> CPSKon r m a
  ObjectKon :: SGPico -> (SGPico -> m SGCall) -> CPSKon SGCall m SGPico
instance FFMorphism (KFun r) (CPSKon r) where
  ffmorph (KFun mk) = MetaKon mk
instance FFMorphism (CPSKon r) (KFun r) where
  ffmorph :: CPSKon r ~~> KFun r
  ffmorph (MetaKon mk) = KFun mk
  ffmorph (ObjectKon _ mk) = KFun mk
instance FFIsomorphism (KFun r) (CPSKon r) where
instance Balloon CPSKon SGCall where
  inflate :: (Monad m) => CPSKon SGCall m ~> CPSKon SGCall (OpaqueKonT CPSKon SGCall m)
  inflate (MetaKon mk) = MetaKon $ \ a -> makeMetaKonT $ \ k -> k *$ mk a
  inflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> makeMetaKonT $ \ k -> k *$ mk ax
  deflate :: (Monad m) => CPSKon SGCall (OpaqueKonT CPSKon SGCall m) ~> CPSKon SGCall m
  deflate (MetaKon mk) = MetaKon $ \ a -> runMetaKonTWith return $ mk a
  deflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> evalOpaqueKonT $ mk ax

letAtom :: (M m) => String -> SGAtom -> m SGPico
letAtom n a = do
  i <- nextL callIDL
  x <- fresh n
  modifyC (return . StampedFix i . Let x a) $ 
    return $ Var x

reify :: (M m) => CPSKon SGCall m SGPico -> m SGPico
reify (MetaKon mk) = do
  x <- fresh "x"
  c <- mk $ Var x
  i <- nextL callIDL
  letAtom "k" $ Stamped i $ LamK x c
reify (ObjectKon k _) = return k

reflect :: (M m) => SGPico -> CPSKon SGCall m SGPico
reflect kx = ObjectKon kx $ \ ax -> do
  i <- nextL callIDL
  return $ StampedFix i $ AppK kx ax

cpsM :: (M m) => SExp -> m SGPico
cpsM (StampedFix i e0) = case e0 of
  L.Lit l -> 
    return $ Lit l
  L.Var x -> do
    let sx = sgNameFromSName x
    return $ Var sx
  L.Lam x e -> do
    let sx = sgNameFromSName x
    kx <- fresh "k"
    c <- withOpaqueC (reflect $ Var kx) $ cpsM e
    letAtom "f" $ Stamped i $ LamF sx kx c
  L.Prim o e -> do
    ex <- cpsM e
    letAtom "a" $ Stamped i $ Prim o ex
  L.Let x e b -> do
    ea <- cpsAtomM e
    let sx = sgNameFromSName x
    callOpaqueCC $ \ (ko :: CPSKon SGCall m SGPico) -> do
      bc <- withOpaqueC ko $ cpsM b
      return $ StampedFix i $ Let sx ea bc
  L.App f e -> do
    callOpaqueCC $ \ (ko :: CPSKon SGCall m SGPico) -> do
      fx <- cpsM f
      ex <- cpsM e
      ka <- reify ko
      return $ StampedFix i $ AppF fx ex ka
  L.If ce te fe -> do
    callOpaqueCC $ \ (ko :: CPSKon SGCall m SGPico) -> do
      cx <- cpsM ce
      ko' <- reflect ^$ reify ko
      tc <- withOpaqueC ko' $ cpsM te
      fc <- withOpaqueC ko' $ cpsM fe
      return $ StampedFix i $ If cx tc fc

cpsAtomM :: (M m) => SExp -> m SGAtom
cpsAtomM se@(StampedFix i e0) = Stamped i ^$ case e0 of
  L.Lam x e -> do
    let sx = sgNameFromSName x
    kx <- fresh "k"
    c <- withOpaqueC (reflect $ Var kx) $ cpsM e
    return $ LamF sx kx c
  L.Prim o e -> do
    ea <- cpsM e
    return $ Prim o ea
  _ -> do
    ex <- cpsM se
    return $ Pico ex

newtype StStateT m a = StStateT { unStStateT :: StateT St m a }
  deriving
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadStateI St, MonadStateE St, MonadState St
    , MonadReaderI r, MonadReaderE r, MonadReader r
    )
instance (Monad m) => MonadStateE Stamp.St (StStateT m) where
  stateE :: StateT Stamp.St (StStateT m) ~> StStateT m
  stateE = stateE . stateLens stampL
  
evalStStateT :: (Functor m) => St -> StStateT m a -> m a
evalStStateT s = evalStateT s . unStStateT

stampCPS :: Exp -> (SExp, SGCall)
stampCPS e = runReader Stamp.env0 $ evalStStateT st0 $ do
  se <- Stamp.stampM e
  c <- runMetaKonT (cpsM se) $ \ ex -> do
    i <- nextL callIDL
    return $ StampedFix i $ Halt ex
  return (se, c)

cps :: Exp -> SGCall
cps = snd . stampCPS
