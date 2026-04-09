/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Remove

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

/-! ## Frame tactic infrastructure -/

/-- Core lemma: frame hypothesis R against goal, leaving residual Q.
Takes the frame proof explicitly. -/
theorem tac_frame' [BI PROP] {P P' R Q goal : PROP} {p : Bool}
    (h_frame : □?p R ∗ Q ⊢ goal)
    (h_rem : P ⊣⊢ P' ∗ □?p R)
    (h_cont : P' ⊢ Q) : P ⊢ goal :=
  h_rem.1.trans <| (sep_mono_l h_cont).trans <| sep_symm.trans h_frame

elab "iframe" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { u, prop, bi, e, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  -- Find and remove the hypothesis
  let uniq ← hyps.findWithInfo hyp
  let ⟨e', hyps', _out, out', p, _eq, pf⟩ := hyps.remove true uniq

  -- Synthesize Frame p out' goal residual via mkAppM + synthInstance
  let residualMVar ← mkFreshExprMVar (some prop)
  let frameType ← mkAppOptM ``Frame #[some prop, some p, some bi, some out', some goal, some residualMVar]
  let frameInst ← try
    synthInstance frameType
  catch _ =>
    throwError "iframe: cannot frame {hyp}"
  let residualExpr ← instantiateMVars residualMVar
  have residual : Q($prop) := residualExpr

  -- Get the frame proof: □?p out' ∗ residual ⊢ goal
  -- @Frame.frame {PROP} {p} {inst} {R} {P} {Q} [self] : □?p R ∗ Q ⊢ P
  let framePf ← mkAppOptM ``Frame.frame #[some prop, some p, some bi, some out', some goal, some residual, some frameInst]

  -- Create continuation goal: e' ⊢ residual
  let goals ← Goals.new bi
  let cont ← goals.addGoal hyps' residual

  -- Build proof: @tac_frame' {PROP} [inst] {P} {P'} {R} {Q} {goal} {p} h_frame h_rem h_cont
  let proof ← mkAppOptM ``tac_frame' #[
    some prop, some bi, some e, some e', some out', some residual, some goal, some p,
    some framePf, some pf, some cont]
  mvar.assign proof
  replaceMainGoal (← goals.getGoals)

end Iris.ProofMode
