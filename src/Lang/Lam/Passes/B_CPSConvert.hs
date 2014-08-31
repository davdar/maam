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

type M = StateOpaqueKon St CPSKon SGCall

fresh :: String -> M SGName
fresh x = do
  i <- nextL bdrIDL
  g <- nextL genIDL
  return $ Stamped i $ GName (Just g) $ Name x

data CPSKon s r a where
  MetaKon :: ((a, s) -> (r, s)) -> CPSKon s r a
  ObjectKon :: SGPico -> CPSKon St SGCall SGPico
instance FFMorph CPSKon KK where
  ffmorph' :: CPSKon s r a -> KK s r a
  ffmorph' (MetaKon mk) = KK mk
  ffmorph' (ObjectKon kx) = KK $ \ (ax, St cid bid gid) -> (StampedFix cid $ AppK kx ax, St (psuc cid) bid gid)
instance FFMorph KK CPSKon where
  ffmorph' (KK mk) = MetaKon mk
instance FFIso CPSKon KK

withKont :: CPSKon St SGCall SGPico -> M SGPico -> M SGCall
withKont k aM = do
  st <- get
  let (c, st') = runStateOpaqueKon aM st k
  put st'
  return c

withKontMeta :: ((SGPico, St) -> (SGCall, St)) -> M SGPico -> M SGCall
withKontMeta k aM = withKont (ffmorph' $ KK k) aM

captureKont :: (CPSKon St SGCall SGPico -> M SGCall) -> M SGPico
captureKont kk = StateOpaqueKon $ \ s (k :: CPSKon St SGCall SGPico) -> runStateMetaKon (kk k) s id

captureKontMeta :: (((SGPico, St) -> (SGCall, St)) -> M SGCall) -> M SGPico
captureKontMeta kk = captureKont $ \ (k :: CPSKon St SGCall SGPico) -> kk $ runKK $ ffmorph' k

modifyKont :: (SGCall -> SGCall) -> M SGPico -> M SGPico
modifyKont f aM = captureKont $ \ k -> do 
  c <- withKont k aM
  return $ f c

internalizeKon :: ((a, St) -> (r, St)) -> a -> M r
internalizeKon f a = do
  st <- get
  let (r, st') = f (a, st)
  put st'
  return r

letAtom :: LocNum -> String -> SGAtom -> M SGPico
letAtom i n a = do
  x <- fresh n
  modifyKont (StampedFix i . Let x a) $ 
    return $ Var x

letAtomNoStamp :: String -> SGAtom -> M SGPico
letAtomNoStamp n a = do
  i <- nextL callIDL
  letAtom i n a

reify :: CPSKon St SGCall SGPico -> M SGPico
reify (MetaKon mk) = do
  x <- fresh "x"
  c <- internalizeKon mk $ Var x
  letAtomNoStamp "k" $ LamK x c
reify (ObjectKon k) = return k

reflect :: SGPico -> CPSKon St SGCall SGPico
reflect kx = ObjectKon kx 

cpsM :: SExp -> M SGPico
cpsM (StampedFix i e0) = case e0 of
  L.Lit l -> 
    return $ Lit l
  L.Var x -> do
    let sx = sgNameFromSName x
    return $ Var sx
  L.Lam x e -> do
    let sx = sgNameFromSName x
    kx <- fresh "k"
    c <- withKont (reflect $ Var kx) $ cpsM e
    letAtom i "f" $ LamF sx kx c
  L.Prim o e -> do
    ex <- cpsM e
    letAtom i "a" $ Prim o ex
  L.Let x e b -> do
    ea <- cpsAtomM e
    let sx = sgNameFromSName x
    captureKont $ \ (ko :: CPSKon St SGCall SGPico) -> do
      bc <- withKont ko $ cpsM b
      return $ StampedFix i $ Let sx ea bc
  L.App f e -> do
    captureKont $ \ (ko :: CPSKon St SGCall SGPico) -> do
      fx <- cpsM f
      ex <- cpsM e
      ka <- reify ko
      return $ StampedFix i $ AppF fx ex ka
  L.If ce te fe -> do
    captureKont $ \ (ko :: CPSKon St SGCall SGPico) -> do
      cx <- cpsM ce
      ko' <- reflect <$> reify ko
      tc <- withKont ko' $ cpsM te
      fc <- withKont ko' $ cpsM fe
      return $ StampedFix i $ If cx tc fc

cpsAtomM :: SExp -> M SGAtom
cpsAtomM se@(StampedFix _ e0) = case e0 of
  L.Lam x e -> do
    let sx = sgNameFromSName x
    kx <- fresh "k"
    c <- withKont (reflect $ Var kx) $ cpsM e
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
stampCPS e = 
  let (se, Stamp.St ei bi) = runReader Stamp.env0 $ runStateT Stamp.st0 $ Stamp.stampM e
      c = fst $ runStateMetaKon (cpsM se) (St ei bi 0) $ \ (ex, St ei' bi' gi') ->
        (StampedFix ei $ Halt ex, St (psuc ei') bi' gi')
  in (se, c)
  -- runReader Stamp.env0 $ evalStStateT st0 $ do
  --   se <- Stamp.stampM e
  --   c <- runMetaKonT (cpsM se) $ \ ex -> do
  --     i <- nextL callIDL
  --     return $ StampedFix i $ Halt ex
  --   return (se, c)

cps :: Exp -> SGCall
cps = snd . stampCPS
