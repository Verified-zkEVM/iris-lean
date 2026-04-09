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

/-- Normalization: if goal is `emp ∗ Q`, replace with `Q`. -/
theorem norm_emp_sep_l [BI PROP] {P Q : PROP} (h : P ⊢ Q) : P ⊢ emp ∗ Q :=
  h.trans emp_sep.2

/-- Normalization: if goal is `Q ∗ emp`, replace with `Q`. -/
theorem norm_sep_emp_r [BI PROP] {P Q : PROP} (h : P ⊢ Q) : P ⊢ Q ∗ emp :=
  h.trans sep_emp.2

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
  let framePf ← mkAppOptM ``Frame.frame #[some prop, some p, some bi, some out', some goal, some residual, some frameInst]

  -- Normalize residual: simplify emp ∗ Q → Q and Q ∗ emp → Q
  let mut normalizedResidual := residualExpr
  let mut normLemma : Option Name := none
  if residualExpr.isAppOfArity ``BIBase.sep 4 then
    let lhs := residualExpr.getArg! 2
    let rhs := residualExpr.getArg! 3
    if lhs.isAppOfArity ``BIBase.emp 2 then
      normalizedResidual := rhs
      normLemma := some ``norm_emp_sep_l
    else if rhs.isAppOfArity ``BIBase.emp 2 then
      normalizedResidual := lhs
      normLemma := some ``norm_sep_emp_r
  have normalGoal : Q($prop) := normalizedResidual

  -- Create continuation goal with normalized residual
  let goals ← Goals.new bi
  let cont ← goals.addGoal hyps' normalGoal

  -- Apply normalization lemma if needed
  let cont' ← match normLemma with
    | some lemName =>
      let norm ← mkAppOptM lemName #[some prop, some bi, some e', some normalGoal, some cont]
      pure norm
    | none => pure (cont : Expr)

  -- Build proof: @tac_frame' {PROP} [inst] {P} {P'} {R} {Q} {goal} {p} h_frame h_rem h_cont
  let proof ← mkAppOptM ``tac_frame' #[
    some prop, some bi, some e, some e', some out', some residual, some goal, some p,
    some framePf, some pf, some cont']
  mvar.assign proof
  replaceMainGoal (← goals.getGoals)

end Iris.ProofMode
