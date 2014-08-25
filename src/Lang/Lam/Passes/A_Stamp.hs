module Lang.Lam.Passes.A_Stamp where

import FP
import Lang.Lam.Syntax

data St = St
  { expID :: Int
  , bdrID :: Int
  }
expIDL :: Lens St Int
expIDL = lens expID $ \ s i -> s { expID = i }
bdrIDL :: Lens St Int
bdrIDL = lens bdrID $ \ s i -> s { bdrID = i }
st0 :: St
st0 = St 0 0

data Env = Env
  { bdrEnv :: Map Name Int
  }
bdrEnvL :: Lens Env (Map Name Int)
bdrEnvL = lens bdrEnv $ \ s e -> s { bdrEnv = e }
env0 :: Env
env0 = Env pempty

type M m = (MonadState St m, MonadReader Env m)

newBdr :: (M m) => Name -> m (Env -> Env)
newBdr x = do
  i <- nextL bdrIDL
  return $ update bdrEnvL $ pinsert x i

lookupName :: (M m) => Name -> m SName
lookupName x = do
  xi <- maybe return (nextL bdrIDL) *$ lookup x <$> askL bdrEnvL
  return $ Stamped xi x

stampM :: (M m) => Exp Name -> m (StampedExp SName)
stampM pe = do
  unit StampedFix <@> nextL expIDL <@> case runFix pe of
    Lit l -> return $ Lit l
    Var x -> Var <$> lookupName x
    Lam x e -> do
      i <- nextL bdrIDL
      local (update bdrEnvL $ pinsert x i) $ do
        se <- stampM e
        return $ Lam (Stamped i x) se
    Prim o e -> Prim o <$> stampM e
    App fe e -> unit App <@> stampM fe <@> stampM e
    If e te fe -> unit If <@> stampM e <@> stampM te <@> stampM fe

stamp :: Exp Name -> StampedExp SName
stamp = evalState st0 . runReaderT env0 . stampM
