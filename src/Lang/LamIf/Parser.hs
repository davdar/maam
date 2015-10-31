module Lang.LamIf.Parser where

import FP
import Lang.LamIf.Syntax

data Keyword = KLambda | KIfZero | KThen | KElse | KLet | KIn
makePrisms ''Keyword

data KeywordPunctuation = KPDot | KPPlus | KPMinus | KPDefEqual
makePrisms ''KeywordPunctuation

data Punctuation = PLParen | PRParen
makePrisms ''Punctuation
    
data Token =
    TKeyword Keyword
  | TKeywordPunctuation KeywordPunctuation
  | TPunctuation Punctuation
  | TInteger ℤ
  | TSymbol 𝕊
  | TWhitespace 𝕊
makePrisms ''Token

data SourceExp = SourceExp
  { sourceExpContext ∷ SourceContext Token
  , sourceExpRawExp ∷ PreExp 𝕊 SourceExp 
  }

stripSourceExp ∷ SourceExp → Fixed (PreExp 𝕊)
stripSourceExp (SourceExp _ e) = Fixed $ map stripSourceExp e

instance Pretty SourceExp where
  pretty e = ppVertical
    [ ppHeader "Source:"
    , pretty $ sourceExpContext e
    , ppHeader "AST:"
    , pretty $ stripSourceExp e
    ]

tokKeyword ∷ Parser ℂ Keyword
tokKeyword = mconcat $ map (\ (s,k) → pWord s ≫ return k)
  [ ("lam",KLambda)
  , ("if0",KIfZero)
  , ("then",KThen)
  , ("else",KElse)
  , ("let",KLet)
  , ("in",KIn)
  ]

tokKeywordPunctuation ∷ Parser ℂ KeywordPunctuation
tokKeywordPunctuation = mconcat $ map (\ (s,kp) → pWord s ≫ return kp)
  [ (".",KPDot)
  , ("+",KPPlus)
  , ("-",KPMinus)
  , (":=",KPDefEqual)
  ]

tokPunctuation ∷ Parser ℂ Punctuation
tokPunctuation = mconcat $ map (\ (s,p) → pWord s ≫ return p)
  [ ("(",PLParen)
  , (")",PRParen)
  ]

tokToken ∷ Parser ℂ Token
tokToken = mconcat
  [ construct tKeywordL            ^$ pRender UL              $ pRender (FG darkYellow) tokKeyword
  , construct tKeywordPunctuationL ^$ pRender (FG darkYellow) $ tokKeywordPunctuation
  , construct tPunctuationL        ^$ pRender (FG darkGray)   $ tokPunctuation
  , construct tIntegerL            ^$ pRender (FG darkRed)    $ pInteger
  , construct tSymbolL ∘ 𝕤         ^$ id                      $ pOneOrMoreGreedy pLetter
  , construct tWhitespaceL         ^$ id                      $ pWhitespaceGreedy
  ]

parWhitespace ∷ Parser Token ()
parWhitespace = void $ pShaped "whitespace" $ view tWhitespaceL

parOptionalWhitespace ∷ Parser Token ()
parOptionalWhitespace = void $ pOptionalGreedy parWhitespace

parSurroundOptionalWhitespace ∷ Parser Token a → Parser Token a
parSurroundOptionalWhitespace = pSurrounded parOptionalWhitespace

parSymbol ∷ Parser Token 𝕊
parSymbol = pShaped "symbol" $ view tSymbolL

parLParen ∷ Parser Token ()
parLParen = pShaped "lparen" $ view $ pLParenL ⌾ tPunctuationL

parRParen ∷ Parser Token ()
parRParen = pShaped "rparen" $ view $ pRParenL ⌾ tPunctuationL

parParens ∷ Parser Token a → Parser Token a
parParens = pSurroundedBy parLParen parRParen ∘ parSurroundOptionalWhitespace

foldSourceExp ∷ FullContextAnnotated Token (PreExp 𝕊 SourceExp) → SourceExp
foldSourceExp (FullContextAnnotated pc e) = SourceExp pc e

unfoldSourceExp ∷ SourceExp → FullContextAnnotated Token (PreExp 𝕊 SourceExp)
unfoldSourceExp (SourceExp pc e) = FullContextAnnotated pc e

parMixes ∷ MixfixF Token (FullContextAnnotated Token) (PreExp 𝕊 SourceExp)
parMixes = concat
  [ mixF $ TerminalF $ (fullContextAnnotatedValue ∘ unfoldSourceExp) ^$ parParens parExp
  , mixF $ TerminalF $ EAtom ∘ AInteger ^$ pShaped "integer" $ view tIntegerL
  , mixF $ TerminalF $ EAtom ∘ AVar ^$ parSymbol
  , mixF $ PreF (𝕟 0) $ pAppendError "lambda prefix" $ do
      void $ pShaped "lambda" $ view $ kLambdaL ⌾ tKeywordL
      x ← parSurroundOptionalWhitespace $ pRender (FG darkTeal) parSymbol
      void $ pShaped "dot" $ view $ kPDotL ⌾ tKeywordPunctuationL
      parOptionalWhitespace
      return $ \ (foldSourceExp → e) → EAtom $ ALam x e
  , mixF $ PreF (𝕟 0) $ pAppendError "let prefix" $ do
      void $ pShaped "let" $ view $ kLetL ⌾ tKeywordL
      x ← parSurroundOptionalWhitespace $ pRender (FG darkTeal) parSymbol
      void $ pShaped ":=" $ view $ kPDefEqualL ⌾ tKeywordPunctuationL
      e₁ ← parSurroundOptionalWhitespace parExp
      void $ pShaped "in" $ view $ kInL ⌾ tKeywordL
      parOptionalWhitespace
      return $ \ (foldSourceExp → e₂) → ELet x e₁ e₂
  , mixF $ PreF (𝕟 0) $ pAppendError "if prefix" $ do
      void $ pShaped "if0" $ view $ kIfZeroL ⌾ tKeywordL
      e₁ ← parSurroundOptionalWhitespace parExp
      void $ pShaped "then" $ view $ kThenL ⌾ tKeywordL
      e₂ ← parSurroundOptionalWhitespace parExp
      void $ pShaped "else" $ view $ kElseL ⌾ tKeywordL
      parOptionalWhitespace
      return $ \ (foldSourceExp → e₃) → EIf e₁ e₂ e₃
  , mixF $ InfrF (𝕟 5) $ pAppendError "plus" $ do
      parSurroundOptionalWhitespace $ pShaped "+" $ view $ kPPlusL ⌾ tKeywordPunctuationL
      return $ \ (foldSourceExp → e₁) (foldSourceExp → e₂) → EOp Plus e₁ e₂
  , mixF $ InfF (𝕟 5) $ pAppendError "minus" $ do
      parSurroundOptionalWhitespace $ pShaped "-" $ view $ kPMinusL ⌾ tKeywordPunctuationL
      return $ \ (foldSourceExp → e₁) (foldSourceExp → e₂) → EOp Minus e₁ e₂
  , mixF $ InflF (𝕟 100) $ pAppendError "application" $ do
      parWhitespace
      return $ \ (foldSourceExp → e₁) (foldSourceExp → e₂) → EApp e₁ e₂
  ]

parExp ∷ Parser Token SourceExp
parExp = foldSourceExp ^$ pError "exp" $ mixfixParserF parMixes $ \ eM → do
  (e,pc) ← pCaptureFull eM
  return $ FullContextAnnotated pc e

parseExp ∷ 𝕊 → Doc ⨄ SourceExp
parseExp cs = parse parExp *$ tokenize tokToken $ tokens cs

-- - Old, before I figured out how to plumb comonadic structure for context
--
-- parMixes ∷ Mixfix Token ParsedExp
-- parMixes = concat
--   [ mix $ Terminal $ parCaptureExp $ unfoldAnnotatedExp ^$ parParens parExp
--   , mix $ Terminal $ parCaptureExp $ EAtom ∘ AInteger ^$ pShaped "integer" $ view tIntegerL
--   , mix $ Terminal $ parCaptureExp $ EAtom ∘ AVar ^$ parSymbol
--   , mix $ Pre (𝕟 0) $ do
--       (pc,x) ← pAppendError "lambda prefix" $ pCaptureFull $ do
--         void $ pShaped "lambda" $ view $ kLambdaL ⌾ tKeywordL
--         x ← parSurroundOptionalWhitespace $ pRender (FG darkTeal) parSymbol
--         void $ parDot
--         parOptionalWhitespace
--         return x
--       return $ \ (AnnotatedExp pc' e) → 
--         AnnotatedExp (pc ⧺ pc') $ EAtom $ ALam x $ AnnotatedExp pc' e
--   , mix $ Pre (𝕟 0) $ pAppendError "if prefix" $ do
--       (pc,(e₁,e₂)) ← pCaptureFull $ do
--         void $ pShaped "if0" $ view $ kIfZeroL ⌾ tKeywordL
--         e₁ ← parSurroundOptionalWhitespace parExp
--         void $ pShaped "then" $ view $ kThenL ⌾ tKeywordL
--         e₂ ← parSurroundOptionalWhitespace parExp
--         void $ pShaped "else" $ view $ kElseL ⌾ tKeywordL
--         parOptionalWhitespace
--         return (e₁,e₂)
--       return $ \ (AnnotatedExp pc' e₃) →
--         AnnotatedExp (pc ⧺ pc') $ EIf e₁ e₂ $ AnnotatedExp pc' e₃
--   , mix $ Pre (𝕟 0) $ do
--       (pc,(x,e₁)) ← pAppendError "let prefix" $ pCaptureFull $ do
--         void $ pShaped "let" $ view $ kLetL ⌾ tKeywordL
--         x ← parSurroundOptionalWhitespace $ pRender (FG darkTeal) parSymbol
--         void $ pShaped ":=" $ view $ kPDefEqualL ⌾ tKeywordPunctuationL
--         e₁ ← parSurroundOptionalWhitespace parExp
--         void $ pShaped "in" $ view $ kInL ⌾ tKeywordL
--         parOptionalWhitespace
--         return (x,e₁)
--       return $ \ (AnnotatedExp pc' e₂) → 
--         AnnotatedExp (pc ⧺ pc') $ ELet x e₁ $ AnnotatedExp pc' e₂
--   , mix $ Infr (𝕟 5) $ do
--       (pc,()) ← pCaptureFull $ 
--         parSurroundOptionalWhitespace $ pShaped "+" $ view $ kPPlusL ⌾ tKeywordPunctuationL
--       return $ \ (AnnotatedExp pc₁ e₁) (AnnotatedExp pc₂ e₂) →
--         AnnotatedExp (pc₁ ⧺ pc ⧺ pc₂) $ EOp Plus (AnnotatedExp pc₁ e₁) (AnnotatedExp pc₂ e₂)
--   , mix $ Inf (𝕟 5) $ do
--       (pc,()) ← pCaptureFull $ 
--         parSurroundOptionalWhitespace $ pShaped "-" $ view $ kPMinusL ⌾ tKeywordPunctuationL
--       return $ \ (AnnotatedExp pc₁ e₁) (AnnotatedExp pc₂ e₂) →
--         AnnotatedExp (pc₁ ⧺ pc ⧺ pc₂) $ EOp Minus (AnnotatedExp pc₁ e₁) (AnnotatedExp pc₂ e₂)
--   , mix $ Infl (𝕟 100) $ do
--       (pc,()) ← pCaptureFull $ parWhitespace
--       return $ \ (AnnotatedExp pc₁ e₁) (AnnotatedExp pc₂ e₂) →
--         AnnotatedExp (pc₁ ⧺ pc ⧺ pc₂) $ EApp (AnnotatedExp pc₁ e₁) (AnnotatedExp pc₂ e₂)
--   ]
-- 
-- parExp ∷ Parser Token ParsedExp
-- parExp = pError "exp" $ mixfixParser parMixes

-- parseStringExpIO ∷ 𝕊 → IO ParsedExp
-- parseStringExpIO cs = parseIO parExp *$ tokenizeIO tokToken $ tokens cs

