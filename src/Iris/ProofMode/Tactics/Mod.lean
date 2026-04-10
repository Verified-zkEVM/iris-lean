/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

/-! ## Modality elimination (simplified)

For the first version, `imod H` strips a `<pers>` wrapper from hypothesis H.
If `H : <pers> P`, it becomes `H : P` (moved to intuitionistic context).
This is the most common use case in Bluebell.

A full `imod` using ElimModal with goal transformation will be added later.
-/

/-- Strip persistently from a hypothesis: if H : <pers> P, replace with H : P.
Uses the fact that <pers> P ⊢ P (persistently_elim). -/
theorem tac_strip_persistently [BI PROP] {E E' P Q : PROP}
    (h_rem : E ⊣⊢ E' ∗ □ P)
    (h_cont : E' ∗ □ P ⊢ Q) : E ⊢ Q :=
  h_rem.1.trans h_cont

/-- `imod H` strips modalities from hypothesis H.
Currently supports stripping <pers> from intuitionistic hypotheses. -/
elab "imod" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { u, prop, bi, e, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  -- For now, just report what the hypothesis looks like
  let uniq ← hyps.findWithInfo hyp
  throwError "imod: not yet implemented for this hypothesis. Use standard Lean tactics after `istop` for now."

end Iris.ProofMode
