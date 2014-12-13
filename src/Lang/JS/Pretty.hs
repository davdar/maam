module Lang.JS.Pretty where

import FP
import qualified FP.Pretty as P
import Lang.JS.Syntax
import Lang.JS.StateSpace

makePrettySum ''Op

instance Pretty Lit where
  pretty (B b) = pretty b
  pretty UndefinedL = P.con "ᴜɴᴅᴇғɪɴᴇᴅ"
  pretty NullL = P.con "ɴᴜʟʟ"
  pretty (S s) = pretty s
  pretty (N d) = pretty d

instance (Pretty e) => Pretty (PreExp e) where
  pretty (Lit l) = pretty l
  pretty (Var n) = pretty n
  pretty (Func xs e) = pretty $ VarLam xs e
  pretty (ObjE xes) = pretty $ toMap xes
  pretty (Let xes e) = P.atLevel 0 $ P.hvsep
    [ P.hsep [ P.key "let" 
             , P.collection "[" "]" "," $ mapOn xes $ \ (x,e') -> P.hsep [ pretty x, P.keyPun ":=", P.botLevel $ P.align $ pretty e' ]
             , P.key "in" 
             ]
    , P.align $ pretty e
    ]
  pretty (App e es) = P.app $ pretty e : map pretty es
  pretty (FieldRef e₁ e₂) = P.atLevel 90 $ concat
    [ P.align $ pretty e₁
    , P.pun "["
    , P.botLevel $ P.align $ pretty e₂
    , P.pun "]"
    ]
  pretty (FieldSet e₁ e₂ e₃) = P.atLevel 10 $ P.hsep
    [ P.atLevel 90 $ concat 
        [ P.align $ pretty e₁ 
        , P.pun "[" 
        , P.botLevel $ P.align $ pretty e₂
        , P.pun "]"
        ]
    , P.keyPun "<-"
    , P.align $ pretty e₃
    ]
  pretty (Delete e₁ e₂) = P.atLevel 10 $ P.hsep
    [ P.atLevel 90 $ concat
        [ P.align $ pretty e₁
        , P.pun "["
        , P.botLevel $ P.align $ pretty e₂
        , P.pun "]"
        ]
    , P.keyPun "</-"
    ]
  pretty (RefSet e₁ e₂) = P.atLevel 10 $ P.hsep
    [ P.atLevel 90 $ concat
        [ P.keyPun "*"
        , P.align $ pretty e₁
        ]
    , P.keyPun "<-"
    , P.align $ pretty e₂
    ]
  pretty (Ref e) = P.atLevel 90 $ P.hsep
    [ P.key "ref"
    , P.align $ pretty e
    ]
  pretty (DeRef e) = P.atLevel 90 $ concat
    [ P.keyPun "*"
    , P.align $ pretty e
    ]
  pretty (If e₁ e₂ e₃) = P.atLevel 0 $ P.hvsep
    [ P.hsep [ P.key "if", P.align $ P.botLevel $ pretty e₁ ]
    , P.hsep [ P.key "then", P.align $ P.botLevel $ pretty e₂ ]
    , P.hsep [ P.key "else", P.align $ pretty e₃ ]
    ]
  pretty (Seq e₁ e₂) = P.atLevel 5 $ P.vsep
    [ P.hsep [ P.bump $ P.align $ pretty e₁, P.pun ";" ]
    , P.align $ pretty e₂
    ]
  pretty (While e₁ e₂) = P.atLevel 0 $ P.hvsep
    [ P.hsep [ P.key "while", pretty e₁, P.pun "{" ]
    , concat [ P.space 2, P.botLevel $ P.align $ pretty e₂ ]
    , P.pun "}"
    ]
  pretty (LabelE l e) = P.atLevel 90 $ concat
    [ pretty l
    , P.pun ":"
    , P.align $ pretty e
    ]
  pretty (Break l e) = P.atLevel 90 $ P.hsep
    [ P.key "break"
    , pretty l
    , pretty e
    ]
  pretty (TryCatch e₁ l e₂) = P.atLevel 0 $ P.hvsep
    [ P.hsep [ P.key "try", P.pun "{" ]
    , concat [ P.space 2 , P.botLevel $ P.align $ pretty e₁ ]
    , P.hsep [ P.key "}", pretty l ]
    , P.hsep [ P.key "catch", P.pun "{" ]
    , concat [ P.space 2 , P.botLevel $ P.align $ pretty e₂ ]
    , P.hsep [ P.key "}" ]
    ]
  pretty (TryFinally e₁ e₂) = P.atLevel 0 $ P.hvsep
    [ P.hsep [ P.key "try", P.pun "{" ]
    , concat [ P.space 2, P.botLevel $ P.align $ pretty e₁ ]
    , P.hsep [ P.key "}" ]
    , P.hsep [ P.key "finally", P.pun "{" ]
    , concat [ P.space 2, P.botLevel $ P.align $ pretty e₂ ]
    , P.hsep [ P.key "}" ]
    ]
  pretty (Throw e) = P.atLevel 90 $ P.hsep
    [ P.key "throw"
    , P.align $ pretty e
    ]
  pretty (PrimOp ONumPlus [e₁, e₂]) = P.atLevel 50 $ P.hsep
    [ pretty e₁, P.keyPun "+ₙ", P.bump $ P.align $ pretty e₂ ]
  pretty (PrimOp OStrPlus [e₁, e₂]) = P.atLevel 50 $ P.hsep
    [ pretty e₁, P.keyPun "+ₛ", P.bump $ P.align $ pretty e₂ ]
  pretty (PrimOp o es) = P.app $ pretty o : map pretty es

instance Functorial Pretty PreExp where functorial = W

instance Pretty Frame where
  -- pretty (PrimK o k) = P.app [pretty o, P.lit "□", pretty k]
  pretty (LetK nvs n nes b) = P.atLevel 0 $ P.hvsep
    [ P.hsep [ P.con "let", pretty n, P.keyPun "=", P.lit "□", P.key "in" ]
    , pretty b
    ]
  pretty (AppL a) = P.app [P.lit "□", pretty a]
  pretty (AppR f vs es) = P.app [pretty f, pretty vs, P.lit "□", pretty es]
  pretty (ObjK _vs n _es) = P.app [ P.lit "{ ..."
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
  pretty (WhileL _c b) = P.app [ P.lit "while □ {"
                               , pretty b
                               , P.lit "}"
                               ]
  pretty (WhileR c _b) = P.app [ P.lit "while "
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
  -- Fig 9. Primitive Operations
  pretty (PrimOpK o vs es) = P.app [ pretty o
                                   , pretty vs
                                   , P.lit "□"
                                   , pretty es
                                   ]

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

instance Pretty AValue where
  pretty (LitA l) = pretty l
  pretty NumA = P.con "ℝ"
  pretty StrA = P.con "S"
  pretty (CloA c) = pretty c
  pretty (ObjA o) = pretty o
  pretty (LocA l) = pretty l

