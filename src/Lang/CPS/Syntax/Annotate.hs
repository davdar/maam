module Lang.CPS.Syntax.Annotate where

import FP
import Lang.CPS.Syntax.AST

type U = ReaderT (Map SName Int) (State (Int, Int))

ubdrL :: Lens (Int, Int) Int
ubdrL = fstL

ulocL :: Lens (Int, Int) Int
ulocL = sndL

uenvP :: P (Map SName Int)
uenvP = P

nextLoc :: U Int
nextLoc = do
  i <- getL ulocL
  putL ulocL $ i + 1
  return i

nextBdr :: U Int
nextBdr = do
  i <- getL ubdrL
  putL ubdrL $ i + 1
  return i

uaskBdr :: SName -> U RName
uaskBdr s = do
  -- if it's not in the map, just choose something fresh...
  i <- maybe return nextBdr . lookup s *$ askP uenvP
  return $ RName i s

freshBdr :: SName -> U (U a -> U a)
freshBdr s = do
  i <- nextBdr
  return $ localP uenvP $ pinsert s i
  
uatom :: SAtom -> U RAtom
uatom (Lit l) = unit $ Lit l
uatom (Var n) = Var <$> uaskBdr n
uatom (Prim o a) = Prim o <$> uatom a
uatom (Lam xs c) = do
  bound <- map composeEndo $ mapM freshBdr xs
  bound $ unit Lam <@> mapM uaskBdr xs <@> ucall c

ucall :: SCall -> U RCall
ucall sc = unit RCall <@> nextLoc <@> case runFix sc of
  If a tc fc -> unit If <@> uatom a <@> ucall tc <@> ucall fc
  App a aes -> unit App <@> uatom a <@> mapM uatom aes
  Halt a -> unit Halt <@> uatom a

sr :: SCall -> RCall
sr = evalState (0, 0) . runReaderT pempty . ucall
