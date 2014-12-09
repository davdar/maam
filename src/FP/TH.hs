module FP.TH where

import FP.Core
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

infixl 9 #@
infixl 8 #@|

infixr 1 ==>

class THApp e where (#@) :: e -> e -> e
class THTup e where tup :: [e] -> e

instance THApp Exp where (#@) = AppE
instance THTup Exp where tup = TupE
instance THApp Type where (#@) = AppT
instance THTup Type where tup ts = TupleT (length ts) #@| ts
instance THTup Pat where tup = TupP

(#@|) :: (THApp e) => e -> [e] -> e
(#@|) = foldl (#@)

app :: (THApp e) => e -> [e] -> e
app = (#@|)

(==>) :: Type -> Type -> Type
f ==> x = ArrowT #@ f #@ x

makeList :: [Exp] -> Exp
makeList = foldrFrom (ConE '[]) $ \ e es -> ConE '(:) #@ e #@ es

makeString :: String -> Exp
makeString = LitE . StringL . toChars
      
conName :: Con -> Name
conName (NormalC n _) = n
conName (RecC n _) = n
conName (InfixC _ n _) = n
conName (ForallC _ _ c) = conName c

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV name) = name
tyVarBndrName (KindedTV name _) = name

sclause :: [Pat] -> Exp -> Clause
sclause p b = Clause p (NormalB b) []

smatch :: Pat -> Exp -> Match
smatch p b = Match p (NormalB b) []

coerceSimpleCon :: Con -> Maybe (Name, [Type])
coerceSimpleCon (NormalC name strictTypes) = Just (name, map snd strictTypes)
coerceSimpleCon (RecC name varStrictTypes) = Just (name, map ff varStrictTypes)
  where ff (_,_,x) = x
coerceSimpleCon (InfixC (_, typeL) name (_, typeR)) = Just (name, [typeL, typeR])
coerceSimpleCon (ForallC _ _ _) = Nothing

tyConIL :: Prism Info Dec
tyConIL = Prism
  { coerce = \ case
      TyConI d -> Just d
      _ -> Nothing
  , inject = TyConI
  }

dataDL :: Prism Dec (Cxt, Name, [TyVarBndr], [Con], [Name])
dataDL = Prism
  { coerce = \ case
      DataD cx t args cs ders -> Just (cx, t, args, cs, ders)
      _ -> Nothing
  , inject = \ (cx, t, args, cs, ders) -> DataD cx t args cs ders
  }

newtypeDL :: Prism Dec (Cxt, Name, [TyVarBndr], Con, [Name])
newtypeDL = Prism
  { coerce = \ case
      NewtypeD cx t args c ders -> Just (cx, t, args, c, ders)
      _ -> Nothing
  , inject = \ (cx, t, args, c, ders) -> NewtypeD cx t args c ders
  }

coerceADT :: Dec -> Maybe (Cxt, Name, [TyVarBndr], [Con], [Name])
coerceADT =
  coerce dataDL
  ++
  (ff ^. coerce newtypeDL)
  where
    ff (cx, t, args, c, ders) = (cx, t, args, [c], ders)

coerceSingleConADT :: Dec -> Maybe (Cxt, Name, [TyVarBndr], Con, [Name])
coerceSingleConADT dec = do
  (cx, t, args, cs, ders) <- coerceADT dec
  c <- coerce singleL cs
  return(cx, t, args, c, ders)

recCL :: Prism Con (Name, [VarStrictType])
recCL = Prism
  { coerce = \ case
      RecC n fs -> Just (n, fs)
      _ -> Nothing
  , inject = \ (n, fs) -> RecC n fs
  }
