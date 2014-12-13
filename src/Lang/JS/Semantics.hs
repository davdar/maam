module Lang.JS.Semantics where

import Prelude (truncate)
import FP hiding (Kon, throw)
import Lang.JS.Syntax
import Data.Bits
import Data.Fixed
import Lang.JS.StateSpace

check :: a -> Bool -> a :+: ()
check _err True  = Inr ()
check err  False = Inl err

liftToEither :: l -> Maybe r -> l :+: r
liftToEither l Nothing  = Inl l
liftToEither _ (Just r) = Inr r

notANum :: AValue -> Maybe r -> String :+: r
notANum v =
  liftToEither $ -- (show (pretty v)) ++
  "something cannot be coerced to a number"

mustCoerceToNum :: AValue -> String :+: Double
mustCoerceToNum v = notANum v $ coerce (nL <.> litAL) v

binaryOp :: String
            -> (a -> a -> Set AValue)
            -> AValue
            -> (AValue -> String :+: a)
            -> [AValue]
            -> String :+: (Set AValue)
binaryOp name op bot coerce args =
  case args of
    [v1,v2] ->
      if v1 == bot || v2 == bot
        then Inr $ singleton $ bot
        else do
        n1 <- coerce v1
        n2 <- coerce v2
        Inr $ op n1 n2
    _ -> Inl $ name ++ " must be applied to two arguments"

wrapIt :: (a -> b -> c) -> (c -> d) -> a -> b -> d
wrapIt f g a b = g $ f a b

binaryNumericOp :: String -> (Double -> Double -> Double) -> [AValue] -> String :+: Set AValue
binaryNumericOp name op args =
  binaryOp name (wrapIt op $ singleton . LitA . N) NumA mustCoerceToNum args

binaryNumericComparisonOp :: String -> (Double -> Double -> Bool) -> [AValue] -> String :+: Set AValue
binaryNumericComparisonOp name op args =
  binaryOp name (wrapIt op $ singleton . LitA . B) BoolA mustCoerceToNum args

unaryNumericOp :: String -> (Double -> Double) -> [AValue] -> String :+: Set AValue
unaryNumericOp name op args =
  case args of
    [NumA] ->
      Inr $ singleton NumA
    [v] -> do
      n <- mustCoerceToNum v
      Inr $ singleton $ LitA $ N $ op n
    _ -> Inl $ name ++ " must be applied to two arguments"

evalOp :: Op -> [AValue] -> String :+: Set AValue
evalOp o args = case o of
  OStrPlus  -> undefined -- TODO: string prim ops
  ONumPlus  -> binaryNumericOp "Plus"     (+) args
  OMul      -> binaryNumericOp "Multiply" (-) args
  ODiv      -> binaryNumericOp "Divide"   (-) args
  OMod      -> binaryNumericOp "Modulo"   (mod') args
  OSub      -> binaryNumericOp "Subtract" (-) args
  OLt       -> binaryNumericComparisonOp "LessThan" (<) args
  OStrLt    -> undefined -- TODO: string prim ops
  OBAnd     -> binaryNumericOp "BitwiseAnd" (fromInteger .: ((.&.) `on` Prelude.truncate)) args
  OBOr      -> binaryNumericOp "BitwiseOr"  (fromInteger .: ((.|.) `on` Prelude.truncate)) args
  OBXOr     -> binaryNumericOp "BitwiseXOr" (fromInteger .: (xor `on` Prelude.truncate)) args
  OBNot     -> unaryNumericOp  "BitwiseNot" (fromInteger . complement . Prelude.truncate) args

-- litAL :: Prism AValue Lit
-- numAL :: Prism AValue ()
-- cloAL :: Prism AValue Clo
-- coerce cloAL :: AValue -> Maybe Clo
-- etc. ...

pushFrame :: (Analysis ς m) => Frame -> m ()
pushFrame fr = do
  fp  <- getL konL
  fp' <- nextFramePtr
  modifyL kstoreL $ mapInsertWith (\/) fp' (singleton (fr, fp))
  putL konL fp'

popFrame :: (Analysis ς m) => m Frame
popFrame = do
  fp <- getL konL
  kσ <- getL kstoreL
  (fr, fp') <- mset $ mjoin $ liftMaybeSet $ kσ # fp
  putL konL fp'
  return fr

eval :: (Analysis ς m) => TExp -> m TExp
eval e =
  case stampedFix e of
    Lit l -> kreturn $ singleton $ LitA l
    Var x -> var x
    Func xs b -> kreturn $ singleton $ CloA $ Clo xs b
    ObjE [] -> do
      kreturn $ singleton $ ObjA $ Obj []
    ObjE ((n',e'):nes) -> do
      pushFrame (ObjK [] n' nes)
      return e'
    Let [] b -> do
      return b
    Let ((n,e):nes) b -> do
      pushFrame $ LetK [] n nes b
      return e
    App f args -> do
      pushFrame (AppL args)
      return f
    FieldRef o i -> do
      pushFrame (FieldRefL i)
      return o
    FieldSet o i v -> do
      pushFrame (FieldSetA i v)
      return o
    Delete o i -> do
      pushFrame (DeleteL i)
      return o
    -- Fig 2. Mutable References
    RefSet l v -> do
      pushFrame (RefSetL v)
      return l
    Ref v -> do
      pushFrame RefK
      return v
    DeRef l -> do
      pushFrame DeRefK
      return l
    -- Fig 8. Control Operators
    If c tb fb -> do
      pushFrame $ IfK tb fb
      return c
    Seq e₁ e₂ -> do
      pushFrame $ SeqK e₂
      return e₁
    While c b -> do
      pushFrame $ WhileL c b
      return c
    LabelE ln e -> do
      pushFrame $ LabelK ln
      return e
    Break ln e -> do
      pushFrame $ BreakK ln
      return e
    TryCatch e₁ n e₂ -> do
      pushFrame $ TryCatchK e₂ n
      return e₁
    TryFinally e₁ e₂ -> do
      pushFrame $ TryFinallyL e₂
      return e₁
    Throw e -> do
      pushFrame $ ThrowK
      return e
    -- Fig 9. Primitive Operations
    PrimOp o [] -> do
      returnEvalOp o []
    PrimOp o (arg:args) -> do
      pushFrame $ PrimOpK o [] args
      return arg


bind :: (Analysis ς m) => Name -> Set AValue -> m ()
bind x v = do
  l <- nextLocation
  modifyL envL $ mapInsert x l -- TODO: Is this right?
  modifyL storeL $ mapInsertWith (\/) l v

bindMany :: (Analysis ς m) => [Name] -> [Set AValue] -> m ()
bindMany []     []     = return ()
bindMany (x:xs) (v:vs) = bind x v >> bindMany xs vs
bindMany []     _      = mzero
bindMany _      []     = mzero

kreturn :: (Analysis ς m) => Set AValue -> m TExp
kreturn v = do
  fr <- popFrame
  s <- kreturn' v fr
  return s

snameToString :: Name -> String
snameToString = getName

kreturn' :: forall ς m. (Analysis ς m) => Set AValue -> Frame -> m TExp
kreturn' v fr = case fr of
  LetK nvs n ((n',e'):nes) b -> do
    bind n v
    touchNGo e' $ LetK nvs n' nes b
  LetK nvs n [] b -> do
    bind n v
    return b
  AppL [] ->
    kreturn' v $ AppR v [] []
  AppL (arg:args) ->
    touchNGo arg $ AppR v [] args
  AppR v vs (arg:args) -> do
    touchNGo arg $ AppR v vs args
  AppR fv argvs [] -> do
    Clo xs b <- liftMaybeZero . coerce cloAL *$ mset fv
    bindMany xs argvs
    return b
  ObjK nvs n ((n',e'):nes) -> do
    let nvs' = (snameToString n, v) : nvs
    touchNGo e' $ ObjK nvs' n' nes
  ObjK nvs n [] -> do
    let nvs' = (snameToString n, v) : nvs
        o    = ObjA $ Obj nvs'
    tailReturn $ singleton o
  FieldRefL i -> do
    touchNGo i $ FieldRefR v
  FieldRefR o -> do
    σ <- getL storeL
    let fieldnames = setMap convertToString v
        v' = prototypalLookup σ o *$ fieldnames
    tailReturn v'
  FieldSetA i e -> do
    touchNGo i $ FieldSetN v e
  FieldSetN o e -> do
    touchNGo e $ FieldSetV o v
  FieldSetV o i -> do
    let o' = do
          Obj fields <- coerceObjSet *$ o
          fieldname <- setMap convertToString i
          setMap (ObjA . Obj) $ updateField fieldname fields (flip $ mapModify (\_ -> v))
    tailReturn o'
  DeleteL e -> do
    touchNGo e $ DeleteR v
  DeleteR o -> do
    let o' = do
          Obj fields <- coerceObjSet *$ o
          fieldname <- setMap convertToString v
          setMap (ObjA . Obj) $ updateField fieldname fields (flip $ \k -> filter (\(k',_) -> k' /= k))
    tailReturn o'
  -- Fig 2. Mutable References
  RefSetL e -> do
    touchNGo e $ RefSetR v
  RefSetR l -> do
    σ <- getL storeL
    -- TODO: This cannot possibly be the right way to do this ...
    let locs = l >>= coerceLocSet
        σ'   = foldr (\l -> (\σ -> mapInsertWith (\/) l v σ)) σ locs
    putL storeL σ'
    tailReturn v
  RefK -> do
    l <- nextLocation
    modifyL storeL $ mapInsertWith (\/) l v
    tailReturn $ singleton $ LocA l
  DeRefK -> do
    σ <- getL storeL
    let locs = v >>= coerceLocSet
        v'   = mjoin . liftMaybeSet . index σ *$ locs
    tailReturn v'
  -- Fig 8. Control Operators
  IfK tb fb -> do
    b <- mset $ coerceBool *$ v
    if b
      then return tb
      else return fb
  SeqK e₂ -> do
    return e₂
  WhileL c e -> do
    b <- mset $ coerceBool *$ v
    if b
      then pushFrame (WhileR c e) >> return e
      else tailReturn $ singleton $ LitA UndefinedL
  WhileR c b -> do
    touchNGo c $ WhileL c b
  LabelK _l -> do
    tailReturn v
  BreakK l -> do
    popToLabel l v
  TryCatchK _e₂ _n -> do
    tailReturn v
  TryFinallyL e₂ -> do
    touchNGo e₂ $ TryFinallyR v
  TryFinallyR result -> do
    tailReturn result
  ThrowK -> do
    throw v
  -- Fig 9. Primitive Operators
  PrimOpK o vs (e:es) -> do
    touchNGo e $ PrimOpK o (v:vs) es
  PrimOpK o vs [] -> do
    returnEvalOp o $ reverse $ v:vs

touchNGo :: (Analysis ς m) => TExp -> Frame -> m TExp
touchNGo e fr = do
  pushFrame fr
  return e

tailReturn :: (Analysis ς m) => Set AValue -> m TExp
tailReturn v = popFrame >>= (kreturn' v)

popToLabel :: (Analysis ς m) => Label -> Set AValue -> m TExp
popToLabel l v = do
  fr <- popFrame
  case fr of
    LabelK l' ->
      if l == l'
      then tailReturn v
      else popToLabel l v
    TryFinallyL e -> do
      pushFrame $ BreakK l
      return e
    _ -> popToLabel l v

throw :: (Analysis ς m) => Set AValue -> m TExp
throw v = do
  fr <- popFrame
  case fr of
    TryCatchK e n -> do
      bind n v
      return e
    TryFinallyL e -> do
      pushFrame $ ThrowK
      return e
    _ ->
      throw v

-- NB: The "Nothing" value refers to the top value of strings, i.e. every possible string.
convertToString :: AValue -> Maybe String
convertToString v = case v of
  LitA (B True)   -> Just "true"
  LitA (B False)  -> Just "false"
  LitA UndefinedL -> Just "undefined"
  LitA NullL      -> Just "null"
  LitA (S s)      -> Just s
  LitA (N d)      -> Just $ show d
  NumA            -> Nothing
  StrA            -> Nothing
  BoolA           -> Nothing
  CloA c          -> Nothing -- todo this isnt right, see ToString in ECMAScript docs
  ObjA o          -> Nothing

crossproduct :: [Set AValue] -> Set [AValue]
crossproduct = toSet . sequence . map toList

failIfAnyFail :: (Ord b) => Set (a :+: b) -> a :+: Set b
failIfAnyFail = map toSet . sequence . toList

returnEvalOp :: (Analysis ς m) => Op -> [Set AValue] -> m TExp
returnEvalOp o args =
  let vs  = setMap (evalOp o) (crossproduct args)
      vs' = failIfAnyFail vs
  in case vs' of
    Inl msg -> throw $ singleton $ LitA $ S msg
    Inr vs'' -> tailReturn $ mjoin vs''

-- 1. have this take [AValue] instead of [Set AValue]
-- 2. directly encode the logic of "if we know the string, do the lookup, if not, return all fields"
prototypalLookup :: Store -> Set AValue -> Maybe String -> Set AValue
prototypalLookup σ o maybeFieldname = do
  Obj fields <- coerceObjSet *$ o
  case maybeFieldname of
    -- actually this isn't right, it should recurisvely get all its parents fields
    Nothing -> msum $ map snd fields
    Just fieldname ->
      case fields # fieldname of
        Just v -> v
        Nothing ->
          case fields # "__proto__" of
            Nothing ->
              singleton $ LitA UndefinedL
            Just avs ->
              avs >>= lookupInParent
  where
    lookupInParent av =
      case av of
        LitA NullL ->
          singleton $ LitA UndefinedL
        (LocA l) ->
          case σ # l of
            Nothing -> singleton $ LitA UndefinedL
            Just vs -> prototypalLookup σ vs maybeFieldname
        _ ->
          -- __proto__ has been set to something other than an object
          -- I *think* this case is exactly the same as LitA NullL, but
          -- λJS doesn't actually specify what to do in this case
          singleton $ LitA UndefinedL

updateField :: Maybe String
               -> [(String, Set AValue)]
               -> ([(String, Set AValue)] -> String -> [(String, Set AValue)])
               -> Set [(String, Set AValue)]
updateField ms fields action = case ms of
  Nothing ->
    let fieldnames = fromList $ map fst fields
    in setMap (action fields) fieldnames
  Just fieldname ->
    singleton $ action fields fieldname

var :: (Analysis ς m) => Name -> m TExp
var x = do
  e <- getL envL
  kreturn $ setMap LocA $ liftMaybeSet $ e # x

coerceBool :: AValue -> Set Bool
coerceBool v = msum
  [ do
      liftMaybeSet $ coerce boolAL v
      singleton True <+> singleton False
  , liftMaybeSet $ coerce (bL <.> litAL) v
  ]

coerceObjSet :: AValue -> Set Obj
coerceObjSet = liftMaybeSet . coerce objAL

coerceLocSet :: AValue -> Set Addr
coerceLocSet = liftMaybeSet . coerce locAL

nextLocation :: (Analysis ς m) => m Addr
nextLocation = do
  Addr l <- getL nextAddrL
  putL nextAddrL $ Addr $ l + 1
  return $ Addr l

nextFramePtr :: (Analysis ς m) => m KAddr
nextFramePtr = do
  KAddr ptr <- getL nextKAddrL
  putL nextKAddrL $ KAddr $ ptr + 1
  return $ KAddr ptr
