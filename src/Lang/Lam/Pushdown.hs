module Lang.Lam.Pushdown where

import FP hiding (Kon)
import Lang.Lam.Syntax
import MAAM
import qualified Lang.Lam.SyntaxHelpers as H
import Lang.Lam.Passes.A_Stamp
import qualified FP.Pretty as P
import Lang.Lam.CPS.Instances.PrettySyntax (prettyLam)

data Kon = HaltK
         | PrimK Op Kon
         | LetK SName SExp Kon
         | AppL SExp Kon
         | AppR (Set AValue) Kon
         | IfK SExp SExp Kon
         deriving (Eq, Ord)

instance Pretty Kon where
  pretty (HaltK) = P.con "HALT"
  pretty (PrimK o k) = P.app [pretty o, P.lit "[ ]", pretty k]
  pretty (LetK x b k) = P.app [P.con "let", pretty x, P.lit "= [ ]", pretty b, pretty k]
  pretty (AppL a k) = P.app [P.lit "[ ]", pretty a, pretty k]
  pretty (AppR v k) = P.app [pretty v, P.lit "[ ]", pretty k]
  pretty (IfK tb fb k) = P.app [P.lit "[ ]", pretty tb, pretty fb, pretty k]

instance HasBot Kon where
  bot = HaltK

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
  , MonadStep m
  , JoinLattice (SS m SExp)
  , PartialOrder (SS m SExp)
  , SSC m SExp
  )

type Store = Map SName (Set AValue)

data Clo = Clo
  { arg :: SName
  , body :: SExp
  }
  deriving (Eq, Ord)

instance Pretty Clo where
  pretty (Clo x b) = prettyLam [x] b

data AValue =
  LitA Lit | IA | CloA Clo
  deriving (Eq, Ord)

instance Pretty AValue where
  pretty (LitA l) = pretty l
  pretty IA = P.con "I"
  pretty (CloA c) = pretty c

eval :: (Analysis m) => P m -> SExp -> m SExp
eval _ e =
  case stampedFix e of
    Lit l -> kreturn $ ssingleton $ LitA l
    Var x -> var x
    Lam x b -> kreturn $ ssingleton $ CloA $ Clo x b
    Prim o e' -> do
      modifyP konP (PrimK o)
      return e'
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
    v' <- coerceBool *$ msumVals v
    return $ ifThenElse v' (tb, κ) (fb, κ)

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

execCollect :: (Analysis m) => P m -> SExp -> SS m SExp
execCollect m s = collect (mstep (eval m)) $ munit m s

omega :: Exp
omega = (H.lam "x" (H.v "x" H.@# H.v "x")) H.@# (H.lam "x" (H.v "x" H.@# H.v "x"))

somega :: SExp
somega = stamp omega

type FIguts = StateT Kon (ListSetT (StateT Store ID))
newtype FI a = FI { runFI :: FIguts a }
             deriving ( MonadStateE Kon
                      , MonadZero
                      , MonadPlus
                      , Unit
                      , Functor
                      , Applicative
                      , Product
                      , Bind
                      , Monad
                      )
instance MonadFail FI where
  fail = error . fromChars

instance MonadStep FI where
  type SS FI = SS FIguts
  type SSC FI = SSC FIguts
  mstep f = mstep (runFI . f)
  munit _ = munit (P :: P FIguts)

instance MonadStateE Store FI where
  stateE = FI . mtMap stateE . stateCommute . mtMap runFI

runFI_SS :: Ord a => SS FI a -> (Set (a, Kon), Store)
runFI_SS = mapFst (cmap runPairWith) . runPairWith . runID . runCompose . runCompose . runCompose

result = runFI_SS $ execCollect (P :: P FI) somega
