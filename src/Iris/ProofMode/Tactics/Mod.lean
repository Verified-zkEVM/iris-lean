/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Iris.ProofMode.Tactics.Basic
import Iris.ProofMode.Tactics.Move

namespace Iris.ProofMode
open Lean Elab Tactic Meta Qq BI Std

/-! ## Modality elimination tactic

`imod H` eliminates a modality from hypothesis H.
For example, if H : <pers> P, it becomes H : P.

This uses the `Replaces` mechanism from Move.lean to safely
replace the hypothesis while maintaining proof soundness.
-/

/-- Replace a hypothesis with something it entails. -/
theorem replaces_of_entails [BI PROP] {A B Q : PROP}
    (h : A ⊢ B) : Replaces Q A B :=
  wand_mono_l h

/-- In an affine logic, <pers> P ⊢ P. -/
theorem persistently_elim_affine [BI PROP] [BIAffine PROP] {P : PROP} :
    iprop(<pers> P) ⊢ P :=
  (and_intro .rfl affine).trans <| persistently_and_l.trans sep_emp.1

/-- `imod H` strips the outermost modality from hypothesis H.
Currently supports:
- H : <pers> P → H : P (for spatial hypotheses)
-/
elab "imod" colGt hyp:ident : tactic => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some { prop, bi, hyps, goal, .. } := parseIrisGoal? g | throwError "not in proof mode"

  let uniq ← hyps.findWithInfo hyp
  match ← hyps.replace bi goal uniq fun name p ty => do
    -- Check if ty is <pers> P (persistently applied to something)
    if ty.isAppOfArity ``BIBase.persistently 3 then
      have P : Q($prop) := ty.appArg!
      addHypInfo hyp name uniq prop P (isBinder := true)
      -- Construct persistently_elim proof: <pers> P ⊢ P
      let _ ← synthInstanceQ q(BIAffine $prop)
      -- Build entails proof: <pers> P ⊢ P (in affine logic)
      let entailsPf ← mkAppOptM ``persistently_elim_affine #[some prop, some bi, none, some P]
      match matchBool p with
      | .inl _ =>
        -- Intuitionistic: □ <pers> P → □ P
        let affinePf ← mkAppOptM ``affinely_mono #[some prop, some bi, none, none, some entailsPf]
        let replPf ← mkAppOptM ``replaces_of_entails #[some prop, some bi, none, none, some goal, some affinePf]
        return .main q(iprop(□ $ty)) q(iprop(□ $P)) (.mkHyp bi name uniq p P _) replPf
      | .inr _ =>
        -- Spatial: <pers> P → P
        let replPf ← mkAppOptM ``replaces_of_entails #[some prop, some bi, some ty, some P, some goal, some entailsPf]
        return .main ty P (.mkHyp bi name uniq p P _) replPf
    else
      throwError "imod: hypothesis {hyp} does not have a recognized modality"
  with
  | .none => throwError "imod: hypothesis {hyp} not found"
  | .unchanged _ hyps' =>
    mvar.setType <| IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. }
  | .main _e e' hyps' pf =>
    let m : Q($e' ⊢ $goal) ← mkFreshExprSyntheticOpaqueMVar <|
      IrisGoal.toExpr { prop, bi, hyps := hyps', goal, .. }
    mvar.assign q(Replaces.apply $pf $m)
    replaceMainGoal [m.mvarId!]

end Iris.ProofMode
