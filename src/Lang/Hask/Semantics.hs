module Lang.Hask.Semantics where

import FP

import Lang.Hask.CPS
import Name
import Literal

type Env τ = Map Name (Addr τ)
type Store ν τ = Map (Addr τ) (ν τ)

data Addr τ = Addr
  { addrName :: Name
  , addrTime :: τ
  }

data Clo τ = Clo
  { cloBinders :: [Name]
  , cloBody :: Call
  , cloEnv :: Env τ
  }

class Val ν τ where
  litI :: Literal -> ν τ
  litE :: ν τ -> Maybe (Set Literal)
  cloI :: Clo τ -> ν τ
  cloE :: ν τ -> Maybe (Set (Clo τ))

data 𝒮 ν τ = 𝒮
  { 𝓈Env :: Env τ
  , 𝓈Store :: Store ν τ
  , 𝓈Time :: τ
  }
makeLenses ''𝒮

class
  ( Monad m
  , MonadStateE (𝒮 ν τ) m
  , MonadZero m
  , MonadPlus m
  , Val ν τ
  , Ord (Addr τ)
  , JoinLattice (ν τ)
  ) => Analysis ν τ m | m -> ν , m -> τ where

new :: (Analysis ν τ m) => Name -> m (Addr τ)
new x = do
  τ <- getL 𝓈TimeL
  return $ Addr x τ

bindM :: (Analysis ν τ m) => Name -> ν τ -> m ()
bindM x v = do
  𝓁 <- new x
  modifyL 𝓈EnvL (mapInsert x 𝓁)
  modifyL 𝓈StoreL (mapInsertWith (\/) 𝓁 v)

var :: (Analysis ν τ m) => Name -> m (ν τ)
var x = do
  ρ <- getL 𝓈EnvL
  σ <- getL 𝓈StoreL
  liftMaybeZero $ index σ *$ index ρ $ x

pico :: (Analysis ν τ m) => Pico -> m (ν τ)
pico = \ case
  Var n -> var n
  Lit l -> return $ litI l

atom :: (Analysis ν τ m) => Atom -> m (ν τ)
atom = \ case
  Pico p -> pico p
  LamF x k c -> do
    ρ <- getL 𝓈EnvL
    return $ cloI $ Clo [x, k] c ρ
  LamK x c -> do
    ρ <- getL 𝓈EnvL
    return $ cloI $ Clo [x] c ρ

call :: (Analysis ν τ m) => Call -> m Call
call c = case runFix c of
  Let x a c' -> do
    v <- atom a  
    bindM x v
    return c'
  Letrec xas c' -> undefined
    
  AppF p₁ p₂ p₃ -> undefined
  AppK p₁ p₂ -> undefined
  Case p conxscs -> undefined
