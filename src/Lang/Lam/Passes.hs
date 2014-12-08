module Lang.Lam.Passes where

import FP
import Lang.CPS.Syntax
import Lang.Common
import Lang.Lam.Syntax
import qualified Lang.CPS.Syntax as C
import qualified Lang.Lam.Syntax as L

-- Stamp {{{

data StampSt = StampSt
  { stampExpID :: LocNum
  , stampBdrID :: BdrNum
  }
makeLenses ''StampSt
st0 :: StampSt
st0 = StampSt zer zer

data Env = Env { bdrEnv :: Map Name BdrNum }
makeLenses ''Env
env0 :: Env
env0 = Env mapEmpty

type StampM 𝓈 m = (HasLens 𝓈 StampSt, MonadStateE 𝓈 m, MonadReader Env m)

lookupName :: (StampM 𝓈 m) => Name -> m SName
lookupName x = do
  xi <- maybeElim (nextL $ stampBdrIDL <.> view) return *$ lookup x ^$ askL bdrEnvL
  return $ Stamped xi x

stampM :: (StampM 𝓈 m) => Exp -> m SExp
stampM pe = do
  StampedFix ^@ nextL (stampExpIDL <.> view) <@> case runFix pe of
    L.Lit l -> return $ L.Lit l
    L.Var x -> L.Var ^$ lookupName x
    Lam x e -> do
      i <- nextL (stampBdrIDL <.> view)
      se <- local (update bdrEnvL $ mapInsert x i) $ stampM e
      return $ Lam (Stamped i x) se
    L.Prim o e -> L.Prim o ^$ stampM e
    L.Let x e b -> do
      se <- stampM e
      i <- nextL (stampBdrIDL <.> view)
      sb <- local (update bdrEnvL $ mapInsert x i) $ stampM b
      return $ L.Let (Stamped i x) se sb
    App fe e -> App ^@ stampM fe <@> stampM e
    L.If e te fe -> L.If ^@ stampM e <@> stampM te <@> stampM fe

stamp :: Exp -> SExp
stamp = evalState st0 . runReaderT env0 . stampM

-- }}}

-- CPS Conversion {{{

data CPSSt = CPSSt
  { callID :: LocNum
  , bdrID :: BdrNum
  , genID :: Int
  }
makeLenses ''CPSSt
stampL :: Lens CPSSt StampSt
stampL = lens lin lout
  where
    lin (CPSSt cid bid _) = StampSt cid bid
    lout (CPSSt _ _ gid) (StampSt cid bid) = CPSSt cid bid gid
instance HasLens CPSSt StampSt where
  view = stampL
cpsst0 :: CPSSt
cpsst0 = CPSSt zer zer zer

type CPSM m = (MonadOpaqueKon CPSKon SGCall m, MonadState CPSSt m)

fresh :: (CPSM m) => String -> m SGName
fresh x = do
  i <- nextL bdrIDL
  g <- nextL genIDL
  return $ Stamped i $ GName (Just g) $ Name x

data CPSKon r m a where
  MetaKon :: (a -> m r) -> CPSKon r m a
  ObjectKon :: SGPico -> (SGPico -> m SGCall) -> CPSKon SGCall m SGPico
instance Morphism3 (KFun r) (CPSKon r) where
  morph3 (KFun mk) = MetaKon mk
instance Morphism3 (CPSKon r) (KFun r) where
  morph3 :: CPSKon r ~~> KFun r
  morph3 (MetaKon mk) = KFun mk
  morph3 (ObjectKon _ mk) = KFun mk
instance Isomorphism3 (KFun r) (CPSKon r) where
instance Balloon CPSKon SGCall where
  inflate :: (Monad m) => CPSKon SGCall m ~> CPSKon SGCall (OpaqueKonT CPSKon SGCall m)
  inflate (MetaKon mk) = MetaKon $ \ a -> makeMetaKonT $ \ k -> k *$ mk a
  inflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> makeMetaKonT $ \ k -> k *$ mk ax
  deflate :: (Monad m) => CPSKon SGCall (OpaqueKonT CPSKon SGCall m) ~> CPSKon SGCall m
  deflate (MetaKon mk) = MetaKon $ \ a -> runMetaKonTWith return $ mk a
  deflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> evalOpaqueKonT $ mk ax

letAtom :: (CPSM m) => String -> SGAtom -> m SGPico
letAtom n a = do
  i <- nextL callIDL
  x <- fresh n
  modifyC (return . StampedFix i . C.Let x a) $ 
    return $ C.Var x

reify :: (CPSM m) => CPSKon SGCall m SGPico -> m SGPico
reify (MetaKon mk) = do
  x <- fresh "x"
  c <- mk $ C.Var x
  i <- nextL callIDL
  letAtom "k" $ Stamped i $ LamK x c
reify (ObjectKon k _) = return k

reflect :: (CPSM m) => SGPico -> CPSKon SGCall m SGPico
reflect kx = ObjectKon kx $ \ ax -> do
  i <- nextL callIDL
  return $ StampedFix i $ AppK kx ax

cpsM :: (CPSM m) => SExp -> m SGPico
cpsM (StampedFix i e0) = case e0 of
  L.Lit l -> 
    return $ C.Lit l
  L.Var x -> do
    let sx = sgNameFromSName x
    return $ C.Var sx
  L.Lam x e -> do
    let sx = sgNameFromSName x
    kx <- fresh "k"
    c <- withOpaqueC (reflect $ C.Var kx) $ cpsM e
    letAtom "f" $ Stamped i $ LamF sx kx c
  L.Prim o e -> do
    ex <- cpsM e
    letAtom "a" $ Stamped i $ C.Prim o ex
  L.Let x e b -> do
    ea <- cpsAtomM e
    let sx = sgNameFromSName x
    callOpaqueCC $ \ (ko :: CPSKon SGCall m SGPico) -> do
      bc <- withOpaqueC ko $ cpsM b
      return $ StampedFix i $ C.Let sx ea bc
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
      return $ StampedFix i $ C.If cx tc fc

cpsAtomM :: (CPSM m) => SExp -> m SGAtom
cpsAtomM se@(StampedFix i e0) = Stamped i ^$ case e0 of
  L.Lam x e -> do
    let sx = sgNameFromSName x
    kx <- fresh "k"
    c <- withOpaqueC (reflect $ C.Var kx) $ cpsM e
    return $ LamF sx kx c
  L.Prim o e -> do
    ea <- cpsM e
    return $ C.Prim o ea
  _ -> do
    ex <- cpsM se
    return $ Pico ex

newtype StStateT m a = StStateT { unStStateT :: StateT CPSSt m a }
  deriving
    ( Unit, Functor, Product, Applicative, Bind, Monad
    , MonadStateI CPSSt, MonadStateE CPSSt, MonadState CPSSt
    , MonadReaderI r, MonadReaderE r, MonadReader r
    )
evalStStateT :: (Functor m) => CPSSt -> StStateT m a -> m a
evalStStateT s = evalStateT s . unStStateT

stampCPS :: Exp -> (SExp, SGCall)
stampCPS e = runReader env0 $ evalStStateT cpsst0 $ do
  se <- stampM e
  c <- runMetaKonT (cpsM se) $ \ ex -> do
    i <- nextL callIDL
    return $ StampedFix i $ Halt ex
  return (se, c)

cps :: Exp -> SGCall
cps = snd . stampCPS

-- }}}
