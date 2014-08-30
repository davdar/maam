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

type M m = (MonadStateE St m, MonadOpaqueKon CPSKon SGCall m)

fresh :: (M m) => String -> m SGName
fresh x = do
  i <- nextL bdrIDL
  g <- nextL genIDL
  return $ Stamped i $ GName (Just g) $ Name x

data CPSKon r m a where
  MetaKon :: (a -> m r) -> CPSKon r m a
  ObjectKon :: SGAtom -> (StampedSGAtom -> m SGCall) -> CPSKon SGCall m StampedSGAtom
instance TransformerMorphism (CPSKon SGCall) (K SGCall) where
  ffmorph :: (Monad m) => CPSKon SGCall m ~> K SGCall m
  ffmorph (MetaKon mk) = K mk
  ffmorph (ObjectKon _ mk) = K mk
instance TransformerMorphism (K SGCall) (CPSKon SGCall) where
  ffmorph (K mk) = MetaKon mk

letAtom :: (M m) => String -> StampedSGAtom -> m SGPico
letAtom _ (Stamped _ (Pico p)) = return p
letAtom n (Stamped i a) = do
  x <- fresh n
  modifyOpaqueKon (return . StampedFix i . Let x a) $ 
    return $ Var x

letAtomNoStamp :: (M m) => String -> SGAtom -> m SGPico
letAtomNoStamp n a = do
  i <- nextL callIDL
  letAtom n $ Stamped i a

reify :: (M m) => CPSKon SGCall m StampedSGAtom -> m SGAtom
reify (MetaKon mk) = do
  x <- fresh "x"
  i <- nextL callIDL
  LamK x <$> mk $ Stamped i $ Pico $ Var x
reify (ObjectKon k _) = return k

reflect :: (M m) => SGAtom -> CPSKon SGCall m StampedSGAtom
reflect ka = ObjectKon ka $ \ aa -> do
  kx <- letAtomNoStamp "k" ka
  ax <- letAtom "x" aa
  i <- nextL callIDL
  return $ StampedFix i $ AppK kx ax

cpsM :: (M m) => SExp -> m StampedSGAtom
cpsM (StampedFix i e0) = case e0 of
  L.Lit l -> 
    return $ Stamped i $ Pico $ Lit l
  L.Var x -> do
    let sx = sgNameFromSName x
    return $ Stamped i $ Pico $ Var sx
  L.Lam x e -> do
    let sx = sgNameFromSName x
    kx <- fresh "k"
    let ko = reflect $ Pico $ Var kx
    c <- withOpaqueC ko $ cpsM e
    return $ Stamped i $ LamF sx kx c
  L.Prim o e -> do
    ex <- letAtom "a" *$ cpsM e
    return $ Stamped i $ Prim o ex
  L.Let x e b -> do
    callOpaqueCC $ \ (ko :: CPSKon SGCall m StampedSGAtom) -> do
      let sx = sgNameFromSName x
      ea <- cpsM e
      bc <- withOpaqueC ko $ cpsM b
      return $ StampedFix (stampedID ea) $ Let sx (stamped ea) bc
  L.App f e -> do
    callOpaqueCC $ \ (ko :: CPSKon SGCall m StampedSGAtom) -> do
      ka <- reify ko
      fx <- letAtom "f" *$ cpsM f
      ex <- letAtom "x" *$ cpsM e
      return $ StampedFix i $ AppF fx ex ka
  L.If ce te fe -> do
    callOpaqueCC $ \ (ko :: CPSKon SGCall m StampedSGAtom) -> do
      ko' <- reflect . Pico <$> letAtomNoStamp "k" *$ reify ko
      cx <- letAtom "c" *$ cpsM ce
      tc <- withOpaqueC ko' $ cpsM te
      fc <- withOpaqueC ko' $ cpsM fe
      return $ StampedFix i $ If cx tc fc

cpsMPico :: (M m) => String -> SExp -> m SGPico
cpsMPico n se = do
  sa <- cpsM se
  letAtom n sa

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
stampCPS e = 
  runReader Stamp.env0 $ evalStStateT st0 $ do
    se <- Stamp.stampM e
    c <- runMetaKonT (cpsMPico "result" se) $ \ ex -> do
      i <- nextL callIDL
      return $ StampedFix i $ Halt ex
    return (se, c)

cps :: Exp -> SGCall
cps = snd . stampCPS
