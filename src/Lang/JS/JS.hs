module Lang.JS.JS where

import FP hiding (Kon, throw)
import Lang.JS.Syntax
import MAAM
import qualified FP.Pretty as P
import Lang.Common (VarLam(..))

-- what changed
-- msumVals -> mset
-- pmodify -> mapModify (and other friends, no more p prefixing)
-- ssingleton -> singleton

data Frame = LetK SName SExp
           | AppL SExp
           | AppR (Set AValue)
           | ObjK [(String, (Set AValue))] SName [(SName, SExp)]
             -- Array Dereferencing
           | FieldRefL SExp
           | FieldRefR (Set AValue)
             -- Array Assignment
           | FieldSetA SExp         SExp
           | FieldSetN (Set AValue) SExp
           | FieldSetV (Set AValue) (Set AValue)
             -- Property Deletion
           | DeleteL SExp
           | DeleteR (Set AValue)
             -- Fig 2. Mutable References
           | RefSetL SExp
           | RefSetR (Set AValue)
           | RefK
           | DeRefK
             -- Fig 8. Control Operators
           | IfK SExp SExp
           | SeqK SExp
           | WhileL SExp SExp
           | WhileR SExp SExp
           | LabelK Label
           | BreakK Label
           | TryCatchK SExp SName
           | TryFinallyL SExp
           | TryFinallyR (Set AValue)
           | ThrowK
           deriving (Eq, Ord)

newtype FramePtr = FramePtr Int
                   deriving (Eq, Ord, Peano)
newtype Kon = Kon [Frame]
type KStore = Map FramePtr (Frame, FramePtr)

instance Pretty Frame where
  -- pretty (PrimK o k) = P.app [pretty o, P.lit "□", pretty k]
  pretty (LetK x b) = P.app [P.con "let", pretty x, P.lit "= □", pretty b]
  pretty (AppL a) = P.app [P.lit "□", pretty a]
  pretty (AppR v) = P.app [pretty v, P.lit "□"]
  pretty (ObjK vs n es) = P.app [ P.lit "{ ..."
                                , pretty n
                                , P.lit ":"
                                , P.lit "□ ,"
                                , P.lit "... }"
                                ]
  -- Array Dereferencing
  pretty (FieldRefL i) = P.app [ P.lit "□"
                               , P.lit "["
                               , pretty i
                               , P.lit "]"
                               ]
  pretty (FieldRefR a) = P.app [ pretty a
                               , P.lit "["
                               , P.lit "□"
                               , P.lit "]"
                               ]
  -- Array Assignment
  pretty (FieldSetA   i e) = P.app [ P.lit "□"
                                   , P.lit "["
                                   , pretty i
                                   , P.lit "]"
                                   , P.lit "="
                                   , pretty e
                                   ]
  pretty (FieldSetN a   e) = P.app [ pretty a
                                   , P.lit "["
                                   , P.lit "□"
                                   , P.lit "]"
                                   , P.lit "="
                                   , pretty e
                                   ]
  pretty (FieldSetV a v  ) = P.app [ pretty a
                                   , P.lit "["
                                   , pretty v
                                   , P.lit "]"
                                   , P.lit "="
                                   , P.lit "□"
                                   ]
  -- Property Deletion
  pretty (DeleteL e) = P.app [ P.lit "delete"
                             , P.lit "□"
                             , P.lit "["
                             , pretty e
                             , P.lit "]"
                             ]
  pretty (DeleteR a) = P.app [ P.lit "delete"
                             , pretty a
                             , P.lit "["
                             , P.lit "□"
                             , P.lit "]"
                             ]
  -- Fig 2. Mutable References
  pretty (RefSetL e) = P.app [ P.lit "□"
                             , P.lit " := "
                             , pretty e
                             ]
  pretty (RefSetR v)  = P.app [ pretty v
                              , P.lit " := "
                              , P.lit "□"
                              ]
  pretty RefK = P.lit "RefK"
  pretty DeRefK = P.lit "DeRefK"
  -- Fig 8. Control Operators
  pretty (IfK tb fb) = P.app [ P.lit "□"
                             , pretty tb
                             , pretty fb
                             ]
  pretty (SeqK e) = P.app [ P.lit "□ ;"
                          , pretty e
                          ]
  pretty (WhileL c b) = P.app [ P.lit "while □ {"
                              , pretty b
                              , P.lit "}"
                              ]
  pretty (WhileR c b) = P.app [ P.lit "while "
                              , pretty c
                              , P.lit "{"
                              , P.lit "□"
                              , P.lit "}"
                              ]
  pretty (LabelK l) = P.app [ P.lit "label"
                            , pretty l
                            , P.lit ": □"
                            ]
  pretty (BreakK l) = P.app [ P.lit "break"
                            , pretty l
                            , P.lit ":"
                            , P.lit ": □"
                            ]
  pretty (TryCatchK e n) = P.app [ P.lit "try"
                                 , P.lit "{"
                                 , P.lit "□"
                                 , P.lit "}"
                                 , P.lit "catch"
                                 , P.lit "("
                                 , pretty n
                                 , P.lit ")"
                                 , P.lit "}"
                                 , pretty e
                                 , P.lit "}"
                                 ]
  pretty (TryFinallyL e) = P.app [ P.lit "try"
                                 , P.lit "{"
                                 , P.lit "□"
                                 , P.lit "}"
                                 , P.lit "finally"
                                 , P.lit "{"
                                 , pretty e
                                 , P.lit "}"
                                 ]
  pretty (TryFinallyR v) = P.app [ P.lit "try"
                                 , P.lit "{"
                                 , pretty v
                                 , P.lit "}"
                                 , P.lit "finally"
                                 , P.lit "{"
                                 , P.lit "□"
                                 , P.lit "}"
                                 ]
  pretty ThrowK = P.app [ P.lit "throw" ]

class
  ( Monad m
  , MonadStateE Σ m
  , MonadZero m
  , MonadPlus m
  , MonadStep ς m
  , JoinLattice (ς SExp)
  , Inject ς
  , PartialOrder (ς SExp)
  ) => Analysis ς m | m -> ς where

type Env = Map SName Loc

type Store = Map Loc (Set AValue)

data Clo = Clo
  { arg :: SName
  , body :: SExp
  }
  deriving (Eq, Ord)

data Obj = Obj
  { fields :: [(String, (Set AValue))]
  }
  deriving (Eq, Ord)

newtype Loc = Loc Int
            deriving (Eq, Ord, Pretty)

instance (Eq a) => (Indexed a v [(a, v)]) where
  -- O(n)
  ((s,v):alist) # s'
    | s == s'   = Just v
    | otherwise = alist # s
  [] # _        = Nothing

instance (Eq a) => (MapLike a v [(a, v)]) where
  -- fuck it

instance Pretty Clo where
  pretty (Clo x b) = pretty $ VarLam [x] b
instance Pretty Obj where
  pretty (Obj fds) =
    P.nest 2 $ P.hvsep
    [ P.lit "{"
    , exec [P.hsep $
            map (\(n,e) ->
                  exec [ pretty n
                       , P.lit ":"
                       , pretty e
                       ])
                fds]
    , P.lit "}"
    ]

data AValue =
    LitA Lit
  | NumA
  | StrA
  | CloA Clo
  | ObjA Obj
    -- Fig 2. Mutable References
  | LocA Loc
  deriving (Eq, Ord)

instance Pretty AValue where
  pretty (LitA l) = pretty l
  pretty NumA = P.con "ℝ"
  pretty StrA = P.con "S"
  pretty (CloA c) = pretty c
  pretty (ObjA o) = pretty o
  pretty (LocA l) = pretty l

data Σ = Σ {
    store :: Store
  , env :: Env
  , kstore :: KStore
  , kon :: FramePtr
  , nextLoc :: Loc
  , nextFP :: Int
  }

makeLenses ''Σ

pushFrame :: (Analysis ς m) => Frame -> m ()
pushFrame fr = do
  fp  <- getL konL
  fp' <- nextFramePtr
  modifyL kstoreL $ mapInsert fp' (fr, fp)
  putL konL fp

popFrame :: (Analysis ς m) => m Frame
popFrame = do
  fp <- getL konL
  kσ <- getL kstoreL
  (fr, fp') <- liftMaybeZero $ kσ # fp
  putL konL fp'
  return fr

eval :: (Analysis ς m) => SExp -> m SExp
eval e =
  case stampedFix e of
    Lit l -> kreturn $ singleton $ LitA l
    Var x -> var x
    Func x b -> kreturn $ singleton $ CloA $ Clo x b
    ObjE [] -> do
      kreturn $ singleton $ ObjA $ Obj []
    ObjE ((n',e'):nes) -> do
      pushFrame (ObjK [] n' nes)
      return e'
    Let x v b -> do
      pushFrame (LetK x b)
      return v
    App f v -> do
      pushFrame (AppL v)
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

bind :: (Analysis ς m) => SName -> Set AValue -> m ()
bind x v = do
  l <- nextLocation
  modifyL envL $ mapInsert x l -- TODO: Is this right?
  modifyL storeL $ mapInsertWith (\/) l v

kreturn :: (Analysis ς m) => Set AValue -> m SExp
kreturn v = do
  fr <- popFrame
  s <- kreturn' v fr
  return s

snameToString :: SName -> String
snameToString = getName . stamped

kreturn' :: (Analysis ς m) => Set AValue -> Frame -> m SExp
kreturn' v fr = case fr of
  LetK x b -> do
    bind x v
    return b
  AppL e -> do
    touchNGo e $ AppR v
  AppR vs -> do
    Clo x b <- coerceClo *$ mset vs
    bind x v
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
    let fieldnames = coerceStrSet *$ v
        v' = prototypalLookup σ o *$ fieldnames
    tailReturn v'
  FieldSetA i e -> do
    touchNGo i $ FieldSetN v e
  FieldSetN o e -> do
    touchNGo e $ FieldSetV o v
  FieldSetV o i -> do
    let o' = do
          Obj fields <- coerceObjSet *$ o
          fieldname <- coerceStrSet *$ i
          singleton $ ObjA $ Obj $
            mapModify (\_ -> v) fieldname fields
    tailReturn o'
  DeleteL e -> do
    touchNGo e $ DeleteR v
  DeleteR o -> do
    let o' = do
          Obj fields <- coerceObjSet *$ o
          fieldname <- coerceStrSet *$ v
          singleton $ ObjA $ Obj $
            filter (\(k,_) -> k /= fieldname) fields
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
    b <- coerceBool *$ mset v
    if b
      then return tb
      else return fb
  SeqK e₂ -> do
    return e₂
  WhileL c e -> do
    b <- coerceBool *$ mset v
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

touchNGo :: (Analysis ς m) => SExp -> Frame -> m SExp
touchNGo e fr = do
  pushFrame fr
  return e

tailReturn :: (Analysis ς m) => Set AValue -> m SExp
tailReturn v = popFrame >>= (kreturn' v)

popToLabel :: (Analysis ς m) => Label -> Set AValue -> m SExp
popToLabel l v = undefined

throw :: (Analysis ς m) => Set AValue -> m SExp
throw v = undefined

prototypalLookup :: Store -> Set AValue -> String -> Set AValue
prototypalLookup σ o fieldname = do
  Obj fields <- coerceObjSet *$ o
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
            Just vs -> prototypalLookup σ vs fieldname
        _ ->
          -- __proto__ has been set to something other than an object
          -- I *think* this case is exactly the same as LitA NullL, but
          -- λJS doesn't actually specify what to do in this case
          singleton $ LitA UndefinedL

var :: (Analysis ς m) => SName -> m SExp
var x = do
  σ <- getL storeL
  e <- getL envL
  kreturn $ mjoin . liftMaybeSet . index σ *$ liftMaybeSet $ e # x

coerceClo :: (Analysis ς m) => AValue -> m Clo
coerceClo (CloA c) = return c
coerceClo _ = mzero

coerceBool :: (Analysis ς m) => AValue -> m Bool
coerceBool (LitA (B b)) = return b
coerceBool _ = mzero

coerceStr :: (Analysis ς m) => AValue -> m String
coerceStr = undefined

coerceStrSet :: AValue -> Set String
coerceStrSet = undefined

coerceObj :: (Analysis ς m) => AValue -> m Obj
coerceObj = undefined

coerceObjSet :: AValue -> Set Obj
coerceObjSet = undefined

coerceLoc :: (Analysis ς m) => AValue -> m Loc
coerceLoc = undefined

coerceLocSet :: AValue -> Set Loc
coerceLocSet = undefined

nextLocation :: (Analysis ς m) => m Loc
nextLocation = undefined

nextFramePtr :: (Analysis ς m) => m FramePtr
nextFramePtr = undefined

-- op :: Op -> Set AValue -> Set AValue
-- op = extend . opOne

-- opOne :: Op -> AValue -> Set AValue
-- opOne Add1 IA = singleton IA
-- opOne Sub1 IA = singleton IA
-- opOne IsNonNeg IA = fromList $ map (LitA . B) [ True, False ]
-- opOne Add1 (LitA (I _)) = singleton IA
-- opOne Sub1 (LitA (I _)) = singleton IA
-- opOne IsNonNeg (LitA (I _)) = fromList $ map (LitA . B) [ True, False ]
-- opOne _ _ = sempty

-- execCollect :: (Analysis ς m) => SExp -> ς SExp
-- execCollect m s = collect (mstep (eval m)) $ munit m s

type FIguts = StateT Σ (ListSetT ID)
newtype FI a = FI { runFI :: FIguts a }
             deriving ( MonadStateE Σ
                      , MonadZero
                      , MonadPlus
                      , Unit
                      , Functor
                      , Applicative
                      , Product
                      , Bind
                      , Monad
                      )
-- instance MonadStep FI where
--   type SS FI = SS FIguts
--   type SSC FI = SSC FIguts
--   mstep f = mstep (runFI . f)
--   munit _ = munit (P :: P FIguts)

-- instance MonadStateE Store FI where
--   stateE = FI . mtMap stateE . stateCommute . mtMap runFI
--
-- runFI_SS :: Ord a => SS FI a -> (Set (a, Kon), Store)
-- runFI_SS = mapFst (cmap runPairWith) . runPairWith . runID . runCompose . runCompose . runCompose

-- result = runFI_SS $ execCollect (P :: P FI) somega
