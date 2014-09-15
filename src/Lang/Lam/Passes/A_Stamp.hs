module Lang.Lam.Passes.A_Stamp where

import FP
import Lang.Lam.Syntax

data St = St
  { expID :: LocNum
  , bdrID :: BdrNum
  }
expIDL :: Lens St LocNum
expIDL = lens expID $ \ s i -> s { expID = i }
bdrIDL :: Lens St BdrNum
bdrIDL = lens bdrID $ \ s i -> s { bdrID = i }
st0 :: St
st0 = St pzero pzero

data Env = Env
  { bdrEnv :: Map Name BdrNum
  }
bdrEnvL :: Lens Env (Map Name BdrNum)
bdrEnvL = lens bdrEnv $ \ s e -> s { bdrEnv = e }
env0 :: Env
env0 = Env pempty

type M m = (MonadStateE St m, MonadReader Env m)

lookupName :: (M m) => Name -> m SName
lookupName x = do
  xi <- maybe (nextL bdrIDL) return *$ lookup x ^$ askL bdrEnvL
  return $ Stamped xi x

stampM :: (M m) => Exp -> m SExp
stampM pe = do
  StampedFix ^@ nextL expIDL <@> case runFix pe of
    Lit l -> return $ Lit l
    Var x -> Var ^$ lookupName x
    Lam x e -> do
      i <- nextL bdrIDL
      se <- local (update bdrEnvL $ pinsert x i) $ stampM e
      return $ Lam (Stamped i x) se
    Prim o e -> Prim o ^$ stampM e
    Let x e b -> do
      se <- stampM e
      i <- nextL bdrIDL
      sb <- local (update bdrEnvL $ pinsert x i) $ stampM b
      return $ Let (Stamped i x) se sb
    App fe e -> App ^@ stampM fe <@> stampM e
    If e te fe -> If ^@ stampM e <@> stampM te <@> stampM fe

stamp :: Exp -> SExp
stamp = evalState st0 . runReaderT env0 . stampM
