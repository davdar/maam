module Lang.Lam.Pushdown where

import FP hiding (Kon)
import Lang.Lam.Syntax

data Kon = HaltK
         | PrimK Op Kon
         | LetK SName SExp Kon
         | AppL SExp Kon
         | AppR (Set AValue) Kon
         | IfK SExp SExp Kon

konP :: P Kon
konP = P

storeP :: P Store
storeP = P

type Analysis m =
  ( MonadStateE Store m
  , MonadStateE Kon m
  , MonadFail m
  , MonadZero m
  , MonadPlus m
  )

type Store = Map SName (Set AValue)

data Clo = Clo
  { arg :: SName
  , body :: SExp
  }
  deriving (Eq, Ord)

data AValue =
  LitA Lit | IA | CloA Clo
  deriving (Eq, Ord)

eval :: (Analysis m) => SExp -> m SExp
eval e =
  case stampedFix e of
    Lit l -> kreturn $ ssingleton $ LitA l
    Var x -> var x
    Lam x b -> kreturn $ ssingleton $ CloA $ Clo x b
    Prim o e -> do
      modifyP konP (PrimK o)
      return e
    Let x v b -> do
      modifyP konP (LetK x v)
      return b
    App f v -> do
      modifyP konP (AppL v)
      return f
    If c tb fb -> do
      modifyP konP (IfK tb fb)
      return c

bind :: (Analysis m) => SName -> Set AValue -> m ()
bind x v = do
  modifyP storeP $ pinsertWith (\/) x v

kreturn :: (Analysis m) => Set AValue -> m SExp
kreturn v = do
  κ <- getP konP
  (s, κ') <- kreturn' κ v
  putP konP κ'
  return s

kreturn' :: (Analysis m) => Kon -> Set AValue -> m (SExp, Kon)
kreturn' k v = case k of
  HaltK -> mzero
  PrimK o κ -> kreturn' κ $ op o v
  LetK x b κ -> do
    bind x v
    return (b, κ)
  AppL e κ -> return (e, AppR v κ)
  AppR vs κ -> do
    Clo x b <- coerceClo *$ msumVals vs
    bind x v
    return (b, κ)
  IfK tb fb κ -> do
    v <- coerceBool *$ msumVals v
    return $ ifThenElse v (tb, κ) (fb, κ)

var :: (Analysis m) => SName -> m SExp
var x = do
  σ <- getP storeP
  kreturn *$ useMaybeZero $ σ # x

coerceClo :: (Analysis m) => AValue -> m Clo
coerceClo (CloA c) = return c
coerceClo _ = mzero

coerceBool :: (Analysis m) => AValue -> m Bool
coerceBool (LitA (B b)) = return b
coerceBool _ = mzero

op :: Op -> Set AValue -> Set AValue
op = extend . opOne

opOne :: Op -> AValue -> Set AValue
opOne Add1 IA = ssingleton IA
opOne Sub1 IA = ssingleton IA
opOne IsNonNeg IA = fromList $ map (LitA . B) [ True, False ]
opOne Add1 (LitA (I _)) = ssingleton IA
opOne Sub1 (LitA (I _)) = ssingleton IA
opOne IsNonNeg (LitA (I _)) = fromList $ map (LitA . B) [ True, False ]
opOne _ _ = sempty
