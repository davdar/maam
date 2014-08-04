module MAAM.M.Monadic where

import FP
import MAAM.M.Delta
import MAAM.M.Syntax
import MAAM.Classes
import MAAM.Common

data CPS
type instance History CPS = Call
cps :: P CPS
cps = P

type MonadCPS val δ addr time μ m = 
  ( MonadZero m
  , MonadPlus m
  , MonadState (Env addr time μ) m
  , MonadState (Store val δ addr time μ) m
  , MonadState (time CPS) m
  , MonadMaybeE m
  , MonadStep m
  , Ord addr
  , Ord (val μ)
  )

type Analysis val δ addr time μ m =
  ( Delta val δ
  , AAM addr time μ
  , MonadCPS val δ addr time μ m
  )

time :: (AAM addr time μ) => P μ -> P 𝓁 -> P (time 𝓁)
time P P = P

env :: (AAM addr time μ) => P μ -> P (Env addr time μ)
env P = P

store :: (AAM addr time μ, Delta val δ) => P δ -> P μ -> P (Store val δ addr time μ)
store P P = P

new :: (Analysis val δ addr time μ m) => P δ -> P μ -> Name -> m addr
new _ μ x = do
  t <- getP $ time μ cps
  return $ alloc μ cps x t

var :: forall val δ addr time μ m. (Analysis val δ addr time μ m) => P δ -> P μ -> Name -> m (Set (val μ))
var δ μ x = do
    e <- getP $ env μ
    s <- getP $ store δ μ
    useMaybe $ do
      index s *$ (index e $ x)

bind :: forall val δ addr time μ m. (Analysis val δ addr time μ m) => P δ -> P μ -> Name -> Set (val μ) -> m ()
bind δ μ x vD = do
  l <- new δ μ x
  modifyP (env μ) $ pinsert x l
  modifyP (store δ μ) $ pinsertWith (\/) l vD

atomic :: (Analysis val δ addr time μ m) => P δ -> P μ -> Atom -> m (Set (val μ))
atomic δ _   (LitA l) = return $ ssingleton $ lit δ l
atomic δ μ (Var x) = var δ μ x
atomic δ μ (Prim o a) = do
  vD <- atomic δ μ a
  return $ vD >>~ op δ o
atomic δ μ (Lam xs c) = mmap (ssingleton . clo δ xs c) $ getP $ env μ

atomicM :: (Analysis val δ addr time μ m) => P δ -> P μ -> Atom -> m (val μ)
atomicM δ μ a = atomic δ μ a >>= msum

call :: (Analysis val δ addr time μ m) => P δ -> P μ -> Call -> m Call
call δ μ (If a tc fc) = do
  b <- atomicM δ μ a >>= elimBoolM δ
  return $ if b then tc else fc
call δ μ (App fa xas) = do
  (xs, c, e') <- atomicM δ μ fa >>= elimCloM δ
  undefined
call _ _ (Halt a) = return $ Halt a

-- exec :: forall z. (MCPS z) => z -> Call -> SS (M z) Call
-- exec z c = 
--   case partialOrderF :: PartialOrderW (SS (M z) Call) of
--     PartialOrderW -> iter f ss0
--   where
--     ss0 = point c
--     f = transition $ call z
-- 
-- collect :: forall z. (MCPS z) => z -> Call -> SS (M z) Call
-- collect z c = case partialOrderF :: PartialOrderW (SS (M z) Call) of
--   PartialOrderW -> case joinLattice1 :: JoinLatticeW (SS (M z) Call) of
--     JoinLatticeW -> iter f ss0
--       where
--         ss0 = point c
--         f = ljoin ss0 . transition (call z)
-- 
-- ----- Concrete
-- 
-- data C = C
-- data CVal = LitC Lit | CloC [Name] Call (Env C)
--   deriving (Eq)
-- instance PartialOrder CVal where
--   pcompare = discreteOrder
-- type instance Addr C = Integer
-- data CAddr = CAddr
-- type instance T CAddr = Integer
-- type instance Val C = CVal
-- type instance M C = StateT (Env C) (StateT (Store C) (StateT Integer Point))
-- 
-- instance Delta C where
--   lit :: C -> Lit -> Val C
--   lit C = LitC
--   clo :: C -> [Name] -> Call -> Env C -> Val C
--   clo C = CloC
--   elimBool :: C -> Val C -> M C Bool
--   elimBool C (LitC (B b)) = return b
--   elimBool C _ = mzero
--   elimClo :: C -> Val C -> M C ([Name], Call, Env C)
--   elimClo C (CloC xs c e) = return (xs, c, e)
--   elimClo C _ = mzero
--   op :: C -> Op -> Val C -> M C (Val C)
--   op C Add1 (LitC (I n)) = return (LitC (I (n+1)))
--   op C Sub1 (LitC (I n)) = return (LitC (I (n-1)))
--   op C IsNonNeg (LitC (I n)) | n >= 0 = return (LitC (B True))
--                              | otherwise = return (LitC (B False))
--   op C _ _ = mzero
-- 
-- c_MCPS :: (forall c. (MCPS c) => c -> a) -> a
-- c_MCPS f = f C
-- 
-- ----- Abstract
-- 
-- data Abstract z = Abstract z
-- data AVal z = IntA | BoolA | CloA [Name] Call (Env z)
-- type instance Addr (Abstract z) = Addr z
-- type instance Val (Abstract z) = AVal z
-- type instance M (Abstract z) = M z
-- 
-- instance (MonadPlus (M z)) => Delta (Abstract z) where
--   lit :: Abstract z -> Lit -> Val (Abstract z)
--   lit _ (I _) = IntA
--   lit _ (B _) = BoolA
--   clo :: Abstract z -> [Name] -> Call -> Env (Abstract z) -> Val (Abstract z)
--   clo _ = CloA
--   elimBool :: Abstract z -> Val (Abstract z) -> M (Abstract z) Bool
--   elimBool _ BoolA = return True `mplus` return False
--   elimBool _ _ = mzero
--   elimClo :: Abstract z -> Val (Abstract z) -> M (Abstract z) ([Name], Call, Env (Abstract z))
--   elimClo _ (CloA xs c e) = return (xs, c, e)
--   elimClo _ _ = mzero
--   op :: Abstract z -> Op -> Val (Abstract z) -> M (Abstract z) (Val (Abstract z))
--   op _ Add1 IntA = return IntA
--   op _ Sub1 IntA = return IntA
--   op _ IsNonNeg IntA = return BoolA
--   op _ _ _ = mzero
-- 
-- ----- 0CFA
-- 
-- data ZCFA = ZCFA
