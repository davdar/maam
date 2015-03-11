module Lang.LamIf.Passes where

import FP
import Lang.LamIf.Syntax as L
import Lang.LamIf.CPS as C

-- Stamp

data StampSt = StampSt
  { stampExpID :: LocNum
  , stampBdrID :: BdrNum
  }
makeLenses ''StampSt
stampSt0 :: StampSt
stampSt0 = StampSt zer zer

data Env = Env { bdrEnv :: Map RawName BdrNum }
makeLenses ''Env
stampEnv0 :: Env
stampEnv0 = Env mapEmpty

type StampM m = (MonadStateE StampSt m, MonadReader Env m)

lookupName :: (StampM m) => RawName -> m SRawName
lookupName x = do
  xi <- elimMaybe (nextL $ stampBdrIDL) return *$ lookup x ^$ askL bdrEnvL
  return $ Stamped xi x

stampM :: (StampM m) => Fix (PreExp RawName) -> m Exp
stampM pe = do
  StampedFix ^@ nextL stampExpIDL <@> case unFix pe of
    L.Lit l -> return $ L.Lit l
    L.Var x -> L.Var ^$ lookupName x
    Lam x e -> do
      i <- nextL stampBdrIDL
      se <- local (update bdrEnvL $ mapInsert x i) $ stampM e
      return $ Lam (Stamped i x) se
    L.Prim o e1 e2 -> return (L.Prim o) <@>  stampM e1 <@> stampM e2
    L.Let x e b -> do
      se <- stampM e
      i <- nextL stampBdrIDL
      sb <- local (update bdrEnvL $ mapInsert x i) $ stampM b
      return $ L.Let (Stamped i x) se sb
    App fe e -> App ^@ stampM fe <@> stampM e
    L.If e te fe -> L.If ^@ stampM e <@> stampM te <@> stampM fe

stamp :: Fix (PreExp RawName) -> StampedFix LocNum (PreExp SRawName)
stamp = evalState stampSt0 . runReaderT stampEnv0 . stampM

-- CPS Conversion

data CPSSt = CPSSt
  { cpsExpID :: LocNum
  , cpsBdrID :: BdrNum
  , cpsGenID :: Int
  }
makeLenses ''CPSSt
stampL :: Lens CPSSt StampSt
stampL = lens lin lout
  where
    lin (CPSSt cid bid _) = StampSt cid bid
    lout (CPSSt _ _ gid) (StampSt cid bid) = CPSSt cid bid gid
cpsSt0 :: CPSSt
cpsSt0 = CPSSt zer zer zer

type CPSM m = (MonadOpaqueKon CPSKon Call m, MonadState CPSSt m)

fresh :: (CPSM m) => String -> m Name
fresh x = do
  i <- nextL cpsBdrIDL
  g <- nextL cpsGenIDL
  return $ Stamped i $ GenName (Just g) $ RawName x

data CPSKon r m a where
  MetaKon :: (a -> m r) -> CPSKon r m a
  ObjectKon :: Pico -> (Pico -> m Call) -> CPSKon Call m Pico
instance Morphism3 (KFun r) (CPSKon r) where
  morph3 (KFun mk) = MetaKon mk
instance Morphism3 (CPSKon r) (KFun r) where
  morph3 :: CPSKon r ~~> KFun r
  morph3 (MetaKon mk) = KFun mk
  morph3 (ObjectKon _ mk) = KFun mk
instance Isomorphism3 (KFun r) (CPSKon r) where
instance Balloon CPSKon Call where
  inflate :: (Monad m) => CPSKon Call m ~> CPSKon Call (OpaqueKonT CPSKon Call m)
  inflate (MetaKon mk) = MetaKon $ \ a -> makeMetaKonT $ \ k -> k *$ mk a
  inflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> makeMetaKonT $ \ k -> k *$ mk ax
  deflate :: (Monad m) => CPSKon Call (OpaqueKonT CPSKon Call m) ~> CPSKon Call m
  deflate (MetaKon mk) = MetaKon $ \ a -> runMetaKonTWith return $ mk a
  deflate (ObjectKon kx mk) = ObjectKon kx $ \ ax -> evalOpaqueKonT $ mk ax

letAtom :: (CPSM m) => String -> Atom -> m Pico
letAtom n a = do
  i <- nextL cpsExpIDL
  x <- fresh n
  modifyC (return . StampedFix i . C.Let x a) $ 
    return $ C.Var x

reify :: (CPSM m) => CPSKon Call m Pico -> m Pico
reify (MetaKon mk) = do
  x <- fresh "x"
  c <- mk $ C.Var x
  i <- nextL cpsExpIDL
  letAtom "k" $ Stamped i $ LamK x c
reify (ObjectKon k _) = return k

reflect :: (CPSM m) => Pico -> CPSKon Call m Pico
reflect kx = ObjectKon kx $ \ ax -> do
  i <- nextL cpsExpIDL
  return $ StampedFix i $ AppK kx ax

cpsM :: (CPSM m) => Exp -> m Pico
cpsM (StampedFix i e0) = case e0 of
  L.Lit l -> 
    return $ C.Lit l
  L.Var x -> do
    let sx = srawNameToName x
    return $ C.Var sx
  L.Lam x e -> do
    let sx = srawNameToName x
    kx <- fresh "k"
    c <- withOpaqueC (reflect $ C.Var kx) $ cpsM e
    letAtom "f" $ Stamped i $ LamF sx kx c
  L.Prim o e1 e2 -> do
    a1 <- cpsM e1
    a2 <- cpsM e2
    letAtom "a" $ Stamped i $ C.Prim o a1 a2
  L.Let x e b -> do
    ea <- cpsAtomM e
    let sx = srawNameToName x
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      bc <- withOpaqueC ko $ cpsM b
      return $ StampedFix i $ C.Let sx ea bc
  L.App f e -> do
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      fx <- cpsM f
      ex <- cpsM e
      ka <- reify ko
      return $ StampedFix i $ AppF fx ex ka
  L.If ce te fe -> do
    callOpaqueCC $ \ (ko :: CPSKon Call m Pico) -> do
      cx <- cpsM ce
      ko' <- reflect ^$ reify ko
      tc <- withOpaqueC ko' $ cpsM te
      fc <- withOpaqueC ko' $ cpsM fe
      return $ StampedFix i $ C.If cx tc fc

cpsAtomM :: (CPSM m) => Exp -> m Atom
cpsAtomM se@(StampedFix i e0) = Stamped i ^$ case e0 of
  L.Lam x e -> do
    let sx = srawNameToName x
    kx <- fresh "k"
    c <- withOpaqueC (reflect $ C.Var kx) $ cpsM e
    return $ LamF sx kx c
  L.Prim o e1 e2 -> do
    a1 <- cpsM e1
    a2 <- cpsM e2
    return $ C.Prim o a1 a2
  _ -> do
    ex <- cpsM se
    return $ Pico ex

stampCPS :: Fix (PreExp RawName) -> (Exp, Call)
stampCPS e = runReader stampEnv0 $ evalStateT cpsSt0 $ do
  se <- stateLens stampL $ stampM e
  c <- runMetaKonT (cpsM se) $ \ ex -> do
    i <- nextL cpsExpIDL
    return $ StampedFix i $ Halt ex
  return (se, c)

cps :: Fix (PreExp RawName) -> Call
cps = snd . stampCPS
