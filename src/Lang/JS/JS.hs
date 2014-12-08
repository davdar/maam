module Lang.JS.JS where

import FP hiding (Kon)
import Lang.JS.Syntax
import MAAM
import qualified FP.Pretty as P
import Lang.CPS.Syntax (prettyLam)

-- what changed
-- msumVals -> mset
-- pmodify -> mapModify (and other friends, no more p prefixing)
-- ssingleton -> singleton

data Kon = HaltK
         -- | PrimK Op Kon
         | LetK SName SExp Kon
         | AppL SExp Kon
         | AppR (Set AValue) Kon
         | ObjK [(String, (Set AValue))] SName [(SName, SExp)] Kon
           -- Array Dereferencing
         | FieldRefL SExp         Kon
         | FieldRefR (Set AValue) Kon
           -- Array Assignment
         | FieldSetA SExp         SExp         Kon
         | FieldSetN (Set AValue) SExp         Kon
         | FieldSetV (Set AValue) (Set AValue) Kon
           -- Property Deletion
         | DeleteL SExp         Kon
         | DeleteR (Set AValue) Kon
         -- | IfK SExp SExp Kon
         deriving (Eq, Ord)

instance Pretty Kon where
  pretty (HaltK) = P.con "HALT"
  -- pretty (PrimK o k) = P.app [pretty o, P.lit "□", pretty k]
  pretty (LetK x b k) = P.app [P.con "let", pretty x, P.lit "= □", pretty b, pretty k]
  pretty (AppL a k) = P.app [P.lit "□", pretty a, pretty k]
  pretty (AppR v k) = P.app [pretty v, P.lit "□", pretty k]
  pretty (ObjK vs n es k) = P.app [ P.lit "{ ..."
                                  , pretty n
                                  , P.lit ":"
                                  , P.lit "□ ,"
                                  , P.lit "... }"
                                  ]
  -- Array Dereferencing
  pretty (FieldRefL i k) = P.app [ P.lit "□"
                                 , P.lit "["
                                 , pretty i
                                 , P.lit "]"
                                 ]
  pretty (FieldRefR a k) = P.app [ pretty a
                                 , P.lit "["
                                 , P.lit "□"
                                 , P.lit "]"
                                 ]
  -- Array Assignment
  pretty (FieldSetA   i e k) = P.app [ P.lit "□"
                                     , P.lit "["
                                     , pretty i
                                     , P.lit "]"
                                     , P.lit "="
                                     , pretty e
                                     ]
  pretty (FieldSetN a   e k) = P.app [ pretty a
                                     , P.lit "["
                                     , P.lit "□"
                                     , P.lit "]"
                                     , P.lit "="
                                     , pretty e
                                     ]
  pretty (FieldSetV a v   k) = P.app [ pretty a
                                     , P.lit "["
                                     , pretty v
                                     , P.lit "]"
                                     , P.lit "="
                                     , P.lit "□"
                                     ]
  -- Property Deletion
  pretty (DeleteL e k) = P.app [ P.lit "delete"
                               , P.lit "□"
                               , P.lit "["
                               , pretty e
                               , P.lit "]"
                               ]
  pretty (DeleteR a k) = P.app [ P.lit "delete"
                               , pretty a
                               , P.lit "["
                               , P.lit "□"
                               , P.lit "]"
                               ]
  -- pretty (IfK tb fb k) = P.app [P.lit "□", pretty tb, pretty fb, pretty k]

konP :: P Kon
konP = P

storeP :: P Store
storeP = P

class
  ( Monad m
  , MonadStateE Store m
  , MonadStateE Kon m
  , MonadZero m
  , MonadPlus m
  , MonadStep ς m
  , JoinLattice (ς SExp)
  , Inject ς
  , PartialOrder (ς SExp)
  ) => Analysis ς m | m -> ς where

type Store = Map SName (Set AValue)

data Clo = Clo
  { arg :: SName
  , body :: SExp
  }
  deriving (Eq, Ord)

data Obj = Obj
  { fields :: [(String, (Set AValue))]
  }
  deriving (Eq, Ord)

instance (Eq a) => (Indexed a v [(a, v)]) where
  -- O(n)
  ((s,v):alist) # s'
    | s == s'   = Just v
    | otherwise = alist # s
  [] # _        = Nothing

instance (Eq a) => (MapLike a v [(a, v)]) where
  -- fuck it

instance Pretty Clo where
  pretty (Clo x b) = prettyLam [x] b
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
  deriving (Eq, Ord)

instance Pretty AValue where
  pretty (LitA l) = pretty l
  pretty NumA = P.con "ℝ"
  pretty StrA = P.con "S"
  pretty (CloA c) = pretty c
  pretty (ObjA o) = pretty o

eval :: (Analysis ς m) => P m -> SExp -> m SExp
eval _ e =
  case stampedFix e of
    Lit l -> kreturn $ singleton $ LitA l
    Var x -> var x
    Func x b -> kreturn $ singleton $ CloA $ Clo x b
    ObjE [] -> do
      kreturn $ singleton $ ObjA $ Obj []
    ObjE ((n',e'):nes) -> do
      modifyP konP (ObjK [] n' nes)
      return e'
    -- Prim o e' -> do
    --   modifyP konP (PrimK o)
    --   return e'
    Let x v b -> do
      modifyP konP (LetK x b)
      return v
    App f v -> do
      modifyP konP (AppL v)
      return f
    FieldRef o i -> do
      modifyP konP (FieldRefL i)
      return o
    FieldSet o i v -> do
      modifyP konP (FieldSetA i v)
      return o
    Delete o i -> do
      modifyP konP (DeleteL i)
      return o
    -- If c tb fb -> do
    --   modifyP konP (IfK tb fb)
    --   return c

bind :: (Analysis ς m) => SName -> Set AValue -> m ()
bind x v = do
  modifyP storeP $ mapInsertWith (\/) x v

kreturn :: (Analysis ς m) => Set AValue -> m SExp
kreturn v = do
  κ <- getP konP
  (s, κ') <- kreturn' κ v
  putP konP κ'
  return s

snameToString :: SName -> String
snameToString = getName . stamped

kreturn' :: (Analysis ς m) => Kon -> Set AValue -> m (SExp, Kon)
kreturn' k v = case k of
  HaltK -> mzero
  -- PrimK o κ -> kreturn' κ $ op o v
  LetK x b κ -> do
    bind x v
    return (b, κ)
  AppL e κ ->
    return (e, AppR v κ)
  AppR vs κ -> do
    Clo x b <- coerceClo *$ mset vs
    bind x v
    return (b, κ)
  ObjK nvs n ((n',e'):nes) κ -> do
    let nvs' = (snameToString n, v) : nvs
    return (e', ObjK nvs' n' nes κ)
  ObjK nvs n [] κ -> do
    let nvs' = (snameToString n, v) : nvs
        o    = ObjA $ Obj nvs'
    kreturn' κ $ singleton o
  FieldRefL i κ -> do
    return (i, FieldRefR v κ)
  FieldRefR o κ -> do
    let v' = do
          Obj fields <- coerceObjSet *$ o
          fieldname <- coerceStrSet *$ v
          maybeElim empty id $ fields # fieldname
    kreturn' κ v'
  FieldSetA i e κ -> do
    return (i, FieldSetN v e κ)
  FieldSetN o e κ -> do
    return (e, FieldSetV o v κ)
  FieldSetV o i κ -> do
    let o' = do
          Obj fields <- coerceObjSet *$ o
          fieldname <- coerceStrSet *$ i
          singleton $ ObjA $ Obj $
            mapModify (\_ -> v) fieldname fields
    kreturn' κ o'
  DeleteL e κ -> do
    return (e, DeleteR v κ)
  DeleteR o κ -> do
    let o' = do
          Obj fields <- coerceObjSet *$ o
          fieldname <- coerceStrSet *$ v
          singleton $ ObjA $ Obj $
            filter (\(k,_) -> k /= fieldname) fields
    kreturn' κ o'
  -- IfK tb fb κ -> do
  --   v' <- coerceBool *$ msumVals v
  --   return $ ifThenElse v' (tb, κ) (fb, κ)

var :: (Analysis ς m) => SName -> m SExp
var x = do
  σ <- getP storeP
  kreturn *$ liftMaybeZero $ σ # x

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

-- execCollect :: (Analysis ς m) => P m -> SExp -> ς SExp
-- execCollect m s = collect (mstep (eval m)) $ munit m s

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
