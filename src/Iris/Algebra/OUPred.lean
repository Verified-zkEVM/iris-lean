/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ordered UPred, ported from MoSel (Rocq)
-/

import Iris.Algebra.ORA

namespace Iris
open OFE ORA

/-- The data of an OUPred (ordered uniform predicate) is an indexed proposition over M
that is monotone with respect to the custom ORA ordering `≼ₒ{n}` rather than CMRA inclusion. -/
@[ext]
structure OUPred (M : Type _) [UORA M] where
  holds : Nat → M → Prop
  mono {n1 n2 x1 x2} : holds n1 x1 → OraOrderN n1 x1 x2 → n2 ≤ n1 → holds n2 x2

instance [UORA M] : Inhabited (OUPred M) :=
  ⟨⟨fun _ _ => True, fun _ _ _ => ⟨⟩⟩⟩

instance [UORA M] : CoeFun (OUPred M) (fun _ => Nat → M → Prop) where
  coe x := x.holds

section OUPred

variable [UORA M]

open OUPred

instance : OFE (OUPred M) where
  Equiv P Q := ∀ n x, ✓{n} x → (P n x ↔ Q n x)
  Dist n P Q := ∀ n' x, n' ≤ n → ✓{n'} x → (P n' x ↔ Q n' x)
  dist_eqv := {
    refl _ _ _ _ _ := .rfl
    symm H _ _ A B := (H _ _ A B).symm
    trans H1 H2 _ _ A B := (H1 _ _ A B).trans (H2 _ _ A B) }
  equiv_dist := ⟨
    fun Heqv _ _ _ _ Hvalid => Heqv _ _ Hvalid,
    fun Hdist _ _ Hvalid => Hdist _ _ _ (Nat.le_refl _) Hvalid⟩
  dist_lt Hdist Hlt _ _ Hle Hvalid :=
    Hdist _ _ (Nat.le_trans Hle (Nat.le_of_succ_le Hlt)) Hvalid

theorem ouPred_ne {P : OUPred M} {n} {m₁ m₂} (H : m₁ ≡{n}≡ m₂) : P n m₁ ↔ P n m₂ :=
  ⟨fun H' => P.mono H' (dist_orderN H) (Nat.le_refl _),
   fun H' => P.mono H' (dist_orderN H.symm) (Nat.le_refl _)⟩

theorem ouPred_proper {P : OUPred M} {n} {m₁ m₂} (H : m₁ ≡ m₂) : P n m₁ ↔ P n m₂ :=
  ouPred_ne H.dist

theorem ouPred_holds_ne {P Q : OUPred M} {n₁ n₂ x}
    (HPQ : P ≡{n₂}≡ Q) (Hn : n₂ ≤ n₁) (Hx : ✓{n₂} x) (HQ : Q n₁ x) : P n₂ x :=
  (HPQ _ _ (Nat.le_refl _) Hx).mpr (Q.mono HQ (dist_orderN Dist.rfl) Hn)

instance : IsCOFE (OUPred M) where
  compl c := {
    holds n x := ∀ n', n' ≤ n → ✓{n'} x → (c n') n' x
    mono {n1 n2 x1 x2 HP Hx12 Hn12 n3 Hn23 Hv} := by
      have Hord : OraOrderN n3 x1 x2 := orderN_of_le Hx12 (Nat.le_trans Hn23 Hn12)
      have Hv1 : ✓{n3} x1 := validN_orderN Hv Hord
      refine mono _ ?_ (orderN_of_le Hx12 (Nat.le_trans Hn23 Hn12)) (Nat.le_refl _)
      exact HP _ (Nat.le_trans Hn23 Hn12) Hv1 }
  conv_compl {n c i x} Hin Hv := by
    refine .trans ?_ (c.cauchy Hin _ _ (Nat.le_refl _) Hv).symm
    refine ⟨fun H => H _ (Nat.le_refl _) Hv, fun H n' Hn' Hv' => ?_⟩
    exact (c.cauchy Hn' _ _ (Nat.le_refl _) Hv').mp
      (mono _ H (dist_orderN Dist.rfl) Hn')

end OUPred

end Iris
