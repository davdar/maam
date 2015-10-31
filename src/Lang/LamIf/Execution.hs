module Lang.LamIf.Execution where

import FP
import MAAM
import Lang.LamIf.Semantics
import Lang.LamIf.Domains
import Lang.LamIf.Values
import Lang.LamIf.Monads
import Lang.LamIf.Stamp
import Lang.LamIf.Time

runParams ∷ TimeParam → DomainParam → (DomainParam → MonadParam) → Exp → Doc
runParams t v m e = case m v of
  MonadParam (P ∷ P m) (iso ∷ ς Exp ⇄ ς' Exp) pty (W ∷ W (ExecutionLamIf val (InjectLamIf var) ς' m,LFPLamIf ς)) → 
    pty $ ex t iso (return ∷ a → m a) $ isoFrom iso $ inject $ InjectLamIf (e,LamIfState bot Nothing time₀ bot bot)

runDiffsParams ∷ TimeParam → DomainParam → (DomainParam → MonadParam) → Exp → Doc
runDiffsParams t v m e = case m v of
  MonadParam (P ∷ P m) (iso ∷ ς Exp ⇄ ς' Exp) (pty ∷ ς Exp → Doc) (W ∷ W (ExecutionLamIf val (InjectLamIf var) ς' m,LFPLamIf ς)) → 
    pretty $ map pty $ exDiffs t iso (return ∷ a → m a) $ isoFrom iso $ inject $ InjectLamIf (e,LamIfState bot Nothing time₀ bot bot)
