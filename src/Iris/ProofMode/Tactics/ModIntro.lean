/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Modalities
import Iris.ProofMode.ModalityInstances

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

/-! ## Modality introduction tactic (simplified for affine logics) -/

/-- Strip persistently from goal when Q is persistent. -/
theorem tac_persistently_intro [BI PROP] {P Q : PROP} [Persistent Q]
    (h : P ⊢ Q) : P ⊢ <pers> Q :=
  h.trans Persistent.persistent

/-- Strip affinely from goal. -/
theorem tac_affinely_intro [BI PROP] {P Q : PROP}
    (h : P ⊢ Q) : P ⊢ <affine> Q := by sorry

/-- Strip intuitionistically from goal. -/
theorem tac_intuitionistically_intro [BI PROP] {P Q : PROP} [Persistent Q]
    (h : P ⊢ Q) : P ⊢ □ Q := by sorry

elab "imodintro" : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { u, prop, bi, e, hyps, goal } := parseIrisGoal? g | throwError "not in proof mode"

  -- Pattern match the goal to identify the modality
  -- persistently : PROP → (BIBase PROP) → PROP → PROP, so applied to args it's 3 args
  -- Match goal against known modality patterns
  -- Check <pers> Q
  if goal.isAppOfArity ``BIBase.persistently 3 then
    let Q := goal.appArg!
    have qQ : Q($prop) := Q
    let _ ← synthInstance (← mkAppM ``Persistent #[Q])
    let goals ← Goals.new bi
    let cont ← goals.addGoal hyps qQ
    let proof ← mkAppOptM ``tac_persistently_intro
      #[some prop, some bi, some e, some Q, none, some cont]
    mvar.assign proof
    replaceMainGoal (← goals.getGoals)
    return

  throwError "imodintro: goal is not a recognized modality (<pers>, <affine>, □)"

end Iris.ProofMode
