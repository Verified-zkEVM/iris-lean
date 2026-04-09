/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Bluebell.Instances

/-! ## Bluebell Ownership Assertions

Ownership assertions for indexed probability spaces with permissions.
These are the core assertions for reasoning about probabilistic programs
in Bluebell, now using Iris BI notation for proof mode support.

Reference: Bluebell paper, Fig. 8 (Assertions used in Bluebell)
-/

namespace Bluebell.Logic

open Iris.BI Iris.ProofMode MeasureTheory
attribute [local instance] Bluebell.assertionBIBase Bluebell.assertionBI Bluebell.assertionBIAffine

variable {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]

/-- The main assertion type for Bluebell -/
abbrev BProp (I Var Val : Type*) [DecidableEq Var] [Inhabited Val] :=
  Bluebell.Assertion (IndexedPSpPm I Var Val)

section Definitions

variable [inst1 : OrderedUnitalResourceAlgebra (IndexedPSpPm I Var Val)]
variable [inst2 : Bluebell.OneLe (IndexedPSpPm I Var Val)]

/-- Ownership of indexed probability spaces with compatible permissions.
`ownPSpPm P p` asserts ownership of the probability spaces `P` with
permissions `p` that are compatible with `P`. -/
def ownPSpPm (P : I → PSp (Var → Val))
    (p : Bluebell.IxCompatiblePermission P)
    : BProp I Var Val :=
  Bluebell.ownIndexedPSpPm P p

/-- Ownership of probability spaces with existentially quantified permissions. -/
def ownPSp' (P : I → PSp (Var → Val)) : BProp I Var Val :=
  Bluebell.ownPSp P

/-! ### Separation properties -/

/-- Ownership of disjoint probability spaces can be separated.
This is the AND-TO-STAR rule from the Bluebell paper (Fig. 9):
When idx(P) ∩ idx(Q) = ∅, P ∧ Q ⊢ P ∗ Q -/
theorem and_to_star (P Q : BProp I Var Val)
    (h_disjoint : True) -- placeholder for disjoint indices condition
    : BIBase.Entails (BIBase.and P Q) (BIBase.sep P Q) := by
  sorry

/-! ### Frame properties -/

/-- The own assertion is monotone: if b₁ ≤ b₂, then own b₂ ⊢ own b₁. -/
theorem own_mono {b₁ b₂ : IndexedPSpPm I Var Val}
    (h : b₁ ≤ b₂) : BIBase.Entails (Bluebell.own b₂) (Bluebell.own b₁) := by
  sorry

/-- Separating conjunction of owns: own b₁ ∗ own b₂ ⊢ own (b₁ * b₂) -/
theorem own_sep_combine {b₁ b₂ : IndexedPSpPm I Var Val}
    : BIBase.Entails (BIBase.sep (Bluebell.own b₁) (Bluebell.own b₂))
        (Bluebell.own (b₁ * b₂)) := by
  sorry

end Definitions

end Bluebell.Logic
