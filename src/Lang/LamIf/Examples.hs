module Lang.LamIf.Examples where

import FP
import Lang.LamIf.Parser
import Lang.LamIf.Stamp
import Lang.LamIf.Execution
import Lang.LamIf.Time
import Lang.LamIf.Domains
import Lang.LamIf.Monads

-- Sample Programs

e_id ∷ IO SourceExp
e_id = ioError $ parseExp $ concat $ intersperse "\n" $
  [ "let id := lam x . x"
  , "in id"
  ]

e_bad ∷ IO SourceExp
e_bad = ioError $ parseExp "let id := lam x . y in id"

e_1 ∷ IO SourceExp
e_1 = ioError $ parseExp "let n := (lam x. x + x) 1 in n"

e_2 ∷ IO SourceExp
e_2 = ioError $ parseExp $ concat $ intersperse "\n"
  [ "let x := (1 + 1) - 1 in"
  , "let n := (if0 x then x else 1) in"
  , "let m := (if0 x then x else 1) in"
  , "let r := (if0 x then n + m else 0) in r"
  ]

-- Sample Executions

zcfa_FI ∷ IO ()
zcfa_FI = do
  e ← ioError ∘ stamp *$ e_2
  pprint $ runParams zcfa abstract flowInsensitive e

zcfa_FS ∷ IO ()
zcfa_FS = do
  e ← ioError ∘ stamp *$ e_2
  pprint $ runParams zcfa abstract flowSensitive e

zcfa_PS ∷ IO ()
zcfa_PS = do
  e ← ioError ∘ stamp *$ e_2
  pprint $ runParams zcfa abstract pathSensitive e

stuff ∷ IO ()
stuff = do
  pprint $ runID $ runFlowJoinT action (𝕟 1) 
  where
    action ∷ FlowJoinT ℕ ID ()
    action = do
      x ← get
      modify $ (+x)
      modify $ (+x)
