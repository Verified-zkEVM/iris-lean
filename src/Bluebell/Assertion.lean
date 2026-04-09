import Iris
import Iris.BI.BIBase
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Bluebell.DiscreteCMRA
import Bluebell.MeasureOnSpace

open MeasureTheory

namespace Bluebell

variable {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]

abbrev Assertion (M : Type*) [OrderedUnitalResourceAlgebra M] :=
  UpperSet M

/-- An ordered unital resource algebra where 1 is the bottom element.
This holds for all Bluebell models (PSp, Permission, PSpPm, IndexedPSpPm). -/
class OneLe (M : Type*) [One M] [LE M] where
  one_le : ∀ a : M, 1 ≤ a

export OneLe (one_le)

section Formula

/-- Allows us to write `P a` instead of `a ∈ P` -/
instance {M : Type*} [OrderedUnitalResourceAlgebra M] : FunLike (Assertion M) M Prop where
  coe := fun P => P.carrier
  coe_injective' := by intro P Q h; aesop

variable {M : Type*} [OrderedUnitalResourceAlgebra M]

@[simp]
def BTrue : Assertion M := {
  carrier := {x | True}
  upper' := by aesop
}

@[simp]
def BFalse : Assertion M := {
  carrier := {x | False}
  upper' := by aesop
}

@[simp]
def lift (φ : Prop) : Assertion M := {
  carrier := {x | φ}
  upper' := by aesop
}

@[simp]
def own (b : M) : Assertion M := {
  carrier := {a | b ≤ a}
  upper' := by
    intro x y h₁ h₂
    have : b ≤ x := by aesop
    have : b ≤ y := by grind
    aesop
}

@[simp]
def and (P Q : Assertion M) : Assertion M := {
  carrier := {a | P a ∧ Q a}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

@[simp]
def or (P Q : Assertion M) : Assertion M := {
  carrier := {a | P a ∨ Q a}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

@[simp]
def sep (P Q : Assertion M) : Assertion M := {
  carrier := {a | ∃ b₁ b₂ : M, (b₁ * b₂) ≤ a ∧ P b₁ ∧ Q b₂}
  upper' := by
    intro a b h₁ h₂
    grind
}

@[simp]
def bexists {A : Type*} (K : A → Assertion M) : Assertion M := {
  carrier := {a | ∃ x : A, K x a}
  upper' := by
    intro a b h₁ h₂
    have h₃ : ∃ x : A, K x a := by aesop
    obtain ⟨x, h₃⟩ := h₃
    have := (K x).upper'
    use x
    aesop
}

@[simp]
def bforall {A : Type*} (K : A → Assertion M) : Assertion M := {
  carrier := {a | ∀ x : A, K x a}
  upper' := by
    intro a b h₁ h₂ x
    have h₃ : ∀ x : A, K x a := by aesop
    have := (K x).upper'
    aesop
}

@[simp]
def wand (P Q : Assertion M) : Assertion M := {
  carrier := {a | ∀ b, P b → Q (a * b)}
  upper' := by
    intro a c hac ha b hPb
    have hab : a * b ≤ c * b := mul_left_mono hac
    exact Q.upper' hab (ha b hPb)
}

@[simp]
def bimp (P Q : Assertion M) : Assertion M := {
  carrier := {a | ∀ b, a ≤ b → P b → Q b}
  upper' := by
    intro a c hac ha b hcb hPb
    exact ha b (le_trans hac hcb) hPb
}

@[simp]
def bident : Assertion M := {
  carrier := {a | 1 ≤ a}
  upper' := by
    intro a b hle ha
    simp at *
    apply le_trans <;> aesop
}

@[simp]
def entail (P Q : Assertion M) : Prop :=
  ∀ m, P m → Q m

@[simp]
def bientail (P Q : Assertion M) : Prop :=
  entail P Q ∧ entail Q P

-- Bluebell-specific notation (scoped to avoid conflicts with Iris BI notation)
scoped notation:30 "⊢ " P => entail BTrue P
scoped notation:30 P " ⊢ " Q => entail P Q
scoped notation:30 P " ⊣⊢ " Q => bientail P Q
scoped notation:40 "∀'" K => bforall K
scoped notation:40 "∃'" K => bexists K
scoped notation:50 "⌈" φ "⌉" => lift φ
scoped notation:60 P " ∧' " Q => and P Q
scoped notation:60 P " ∨' " Q => or P Q
scoped notation:70 P:70 " *' " Q:71 => sep P Q

structure CompatiblePermission (P : PSp (Var → Val)) where
  perm : Permission Var
  comp : P.compatiblePerm perm

structure IxCompatiblePermission (P : I → PSp (Var → Val)) where
  perm : I → Permission Var
  comp : ∀ i, (P i).compatiblePerm (perm i)

@[simp]
def ownIndexedPSpPm
  (P : I → PSp (Var → Val))
  (p : IxCompatiblePermission P)
  : Assertion (IndexedPSpPm I Var Val) :=
  own (fun i ↦ ⟨⟨P i, p.perm i⟩, p.comp i⟩)

@[simp]
def ownPSp (P : I → PSp (Var → Val)) : Assertion (IndexedPSpPm I Var Val) :=
  bexists (fun p : IxCompatiblePermission P =>
    ownIndexedPSpPm P p)

-- TODO: complete definition once PSp projection is resolved
@[simp]
def isDistributed {A : Type*} [MeasurableSpace A] (i : I) (E : (Var → Val) → A) (μ : Measure A)
  : Assertion (IndexedPSpPm I Var Val) := sorry

@[simp]
def bProp (I Var Val : Type*) [DecidableEq Var] [Inhabited Val] :=
  Assertion (IndexedPSpPm I Var Val)

end Formula

section Properties

theorem sep_ident {P : bProp I Var Val}
  : P *' BTrue ⊣⊢ P := by
  constructor
  · intro m hm
    have := P.upper'
    sorry
  · sorry

theorem sep_comm {P Q : bProp I Var Val}
  : P *' Q ⊣⊢ Q *' P := by
  constructor
  · intro m hm
    obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
    use b₂, b₁
    have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
    aesop
  · intro m hm
    obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
    use b₂, b₁
    have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
    aesop

variable {M : Type*} [OrderedUnitalResourceAlgebra M]

theorem sep_assoc {P Q R : Assertion M}
  : (P *' Q) *' R ⊢ P *' (Q *' R) := by
  intro m hm
  obtain ⟨pq, r, hpqr, ⟨p, q, hpq, hP, hQ⟩, hR⟩ := hm
  refine ⟨p, q * r, ?_, hP, q, r, le_refl _, hQ, hR⟩
  calc p * (q * r) = (p * q) * r := by rw [mul_assoc]
    _ ≤ pq * r := mul_left_mono hpq
    _ ≤ m := hpqr

theorem sep_mono_l {P P' Q : Assertion M}
    (h : P ⊢ P') : P *' Q ⊢ P' *' Q := by
  intro m ⟨b₁, b₂, hle, hP, hQ⟩
  exact ⟨b₁, b₂, hle, h b₁ hP, hQ⟩

theorem sep_mono_r {P Q Q' : Assertion M}
    (h : Q ⊢ Q') : P *' Q ⊢ P *' Q' := by
  intro m ⟨b₁, b₂, hle, hP, hQ⟩
  exact ⟨b₁, b₂, hle, hP, h b₂ hQ⟩

end Properties

/-! ## OFE / COFE instances for Assertion (discrete) -/

section OFE

variable {M : Type*} [OrderedUnitalResourceAlgebra M]

instance assertionCOFE : Iris.COFE (Assertion M) :=
  Iris.COFE.ofDiscrete Eq ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

end OFE

/-! ## BIBase and BI instances for Assertion -/

section BIInstance

variable {M : Type*} [OrderedUnitalResourceAlgebra M]

/-- Schematic universal quantifier for Assertion -/
def sForallA (Ψ : Assertion M → Prop) : Assertion M := {
  carrier := {a | ∀ p, Ψ p → p a}
  upper' := by
    intro a b hle ha p hΨ
    exact p.upper' hle (ha p hΨ)
}

/-- Schematic existential quantifier for Assertion -/
def sExistsA (Ψ : Assertion M → Prop) : Assertion M := {
  carrier := {a | ∃ p, Ψ p ∧ p a}
  upper' := by
    intro a b hle ⟨p, hΨ, hpa⟩
    exact ⟨p, hΨ, p.upper' hle hpa⟩
}

/-- Persistence modality: □ P holds at a iff P holds at the core (= 1).
In OrderedUnitalResourceAlgebra, pcore x = some 1, so □ P = {a | P 1}. -/
def bpersistently (P : Assertion M) : Assertion M := {
  carrier := {_a | P 1}
  upper' := by intro _ _ _ h; exact h
}

instance assertionBIBase : Iris.BI.BIBase (Assertion M) where
  Entails P Q := ∀ m, P m → Q m
  emp := bident
  pure φ := lift φ
  and := Bluebell.and
  or := Bluebell.or
  imp := bimp
  sForall := sForallA
  sExists := sExistsA
  sep := sep
  wand := wand
  persistently := bpersistently
  later := id

variable [OneLe M]

@[simp] theorem persistently_unfold (P : Assertion M) :
    @Iris.BI.BIBase.persistently (Assertion M) assertionBIBase P = bpersistently P := rfl

@[simp] theorem later_unfold (P : Assertion M) :
    @Iris.BI.BIBase.later (Assertion M) assertionBIBase P = P := rfl

@[simp] theorem entails_unfold (P Q : Assertion M) :
    @Iris.BI.BIBase.Entails (Assertion M) assertionBIBase P Q = (∀ m, P m → Q m) := rfl

@[simp] theorem emp_unfold :
    @Iris.BI.BIBase.emp (Assertion M) assertionBIBase = bident := rfl

@[simp] theorem sep_unfold (P Q : Assertion M) :
    @Iris.BI.BIBase.sep (Assertion M) assertionBIBase P Q = Bluebell.sep P Q := rfl

theorem bpersistently_mem (P : Assertion M) (m : M) :
    (bpersistently P) m ↔ P 1 := by
  constructor <;> intro h <;> exact h

instance assertionBI : Iris.BI (Assertion M) where
  equiv_iff := by
    intro P Q; constructor
    · intro h; exact ⟨fun m hm => h ▸ hm, fun m hm => h ▸ hm⟩
    · intro ⟨hPQ, hQP⟩
      ext m; exact ⟨fun hm => hPQ m hm, fun hm => hQP m hm⟩
  entails_preorder := {
    refl := by intro P m h; exact h
    trans := by intro P Q R hab hbc m hm; exact hbc m (hab m hm)
  }

  -- All NE proofs: discrete OFE (Dist = Eq), so congruence suffices
  and_ne := ⟨fun _ _ _ h₁ _ _ h₂ => .of_eq (by subst h₁; subst h₂; rfl)⟩
  or_ne := ⟨fun _ _ _ h₁ _ _ h₂ => .of_eq (by subst h₁; subst h₂; rfl)⟩
  imp_ne := ⟨fun _ _ _ h₁ _ _ h₂ => .of_eq (by subst h₁; subst h₂; rfl)⟩
  sForall_ne := fun h => Iris.liftRel_eq.mp h ▸ rfl
  sExists_ne := fun h => Iris.liftRel_eq.mp h ▸ rfl
  sep_ne := ⟨fun _ _ _ h₁ _ _ h₂ => .of_eq (by subst h₁; subst h₂; rfl)⟩
  wand_ne := ⟨fun _ _ _ h₁ _ _ h₂ => .of_eq (by subst h₁; subst h₂; rfl)⟩
  persistently_ne := ⟨fun _ _ _ h => .of_eq (by subst h; rfl)⟩
  later_ne := ⟨fun _ _ _ h => h⟩

  -- Pure
  pure_intro := by intro _ _ hφ _ _; exact hφ
  pure_elim' := by intro _ P h m hm; exact h hm m trivial

  -- And
  and_elim_l := by intro _ _ _ ⟨hP, _⟩; exact hP
  and_elim_r := by intro _ _ _ ⟨_, hQ⟩; exact hQ
  and_intro := by intro _ _ _ hPQ hPR m hm; exact ⟨hPQ m hm, hPR m hm⟩

  -- Or
  or_intro_l := by intro _ _ _ hm; exact .inl hm
  or_intro_r := by intro _ _ _ hm; exact .inr hm
  or_elim := by intro _ _ _ hPR hQR _ hm; exact hm.elim (hPR _) (hQR _)

  -- Imp (bimp: {a | ∀ b ≥ a, P b → Q b})
  imp_intro := by
    intro P _ _ hPQR m hPm b hmb hQb
    exact hPQR b ⟨P.upper' hmb hPm, hQb⟩
  imp_elim := by
    intro _ _ _ hPQR m ⟨hPm, hQm⟩
    exact hPQR m hPm m le_rfl hQm

  -- sForall / sExists
  sForall_intro := by intro _ _ h m hPm p hΨp; exact h p hΨp m hPm
  sForall_elim := by intro _ _ hΨp _ hm; exact hm _ hΨp
  sExists_intro := by intro _ _ hΨp _ hm; exact ⟨_, hΨp, hm⟩
  sExists_elim := by intro _ _ h _ ⟨p, hΦp, hpm⟩; exact h p hΦp _ hpm

  -- Sep
  sep_mono := by
    intro _ _ _ _ hPQ hP'Q' _ ⟨b₁, b₂, hle, hP, hP'⟩
    exact ⟨b₁, b₂, hle, hPQ _ hP, hP'Q' _ hP'⟩
  emp_sep := by
    intro P; exact ⟨
      fun _ ⟨b₁, b₂, hle, _, hP⟩ =>
        P.upper' (le_trans (le_mul_of_one_le_left' (one_le b₁)) hle) hP,
      fun m hPm => ⟨1, m, by simp, one_le 1, hPm⟩⟩
  sep_symm := by
    intro _ _ _ ⟨b₁, b₂, hle, hP, hQ⟩
    exact ⟨b₂, b₁, mul_comm b₁ b₂ ▸ hle, hQ, hP⟩
  sep_assoc_l := by
    intro _ _ _ _ ⟨pq, r, hpqr, ⟨p, q, hpq, hP, hQ⟩, hR⟩
    exact ⟨p, q * r, le_trans (mul_assoc p q r ▸ mul_left_mono hpq) hpqr, hP, q, r, le_rfl, hQ, hR⟩

  -- Wand
  wand_intro := by
    intro _ _ _ hPQR m hPm b hQb
    exact hPQR (m * b) ⟨m, b, le_rfl, hPm, hQb⟩
  wand_elim := by
    intro _ _ R hPQR _ ⟨b₁, b₂, hle, hP, hQ⟩
    exact R.upper' hle (hPQR b₁ hP b₂ hQ)

  -- Persistently (bpersistently P = {a | P 1})
  persistently_mono := by intro _ _ h _ hm; exact h 1 hm
  persistently_idem_2 := by intro _ _ hm; exact hm
  persistently_emp_2 := by intro _ _; exact le_refl 1
  persistently_and_2 := by intro _ _ _ hm; exact hm
  persistently_sExists_1 := by
    -- <pers> (sExists Ψ) ⊢ sExists (fun q => ∃ a, ⌜Ψ a⌝ ∧ <pers> a = q)
    -- Both sides reduce to ∃ a, Ψ a ∧ a 1, but with different BIBase wrappers
    intro Ψ m ⟨p, hΨ, hp⟩
    -- Goal: sExists at m of the RHS predicate
    -- We need to provide a witness q and show the predicate holds
    exact ⟨_, ⟨p, rfl⟩, hΨ, hp⟩
  persistently_absorb_l := by intro _ _ _ ⟨_, _, _, hP, _⟩; exact hP
  persistently_and_l := by
    intro P _ _ ⟨hP, hQ⟩
    exact ⟨1, _, by simp, P.upper' (one_le 1) hP, hQ⟩

  -- Later (= id)
  later_mono := by intro _ _ h _ hm; exact h _ hm
  later_intro := by intro _ _ hm; exact hm
  later_sForall_2 := by
    -- (∀ p, ⌜Φ p⌝ → ▷ p) ⊢ ▷ sForall Φ, with later = id:
    -- sForall (fun q => ∃ a, bimp (lift (Φ a)) a = q) at m ⊢ sForall Φ at m
    intro Φ m hm p hΦ
    -- hm : ∀ q, (∃ a, bimp (lift (Φ a)) a = q) → q m
    -- Need: p m, given Φ p
    -- Take q = bimp (lift (Φ p)) p, with witness a = p
    have := hm _ ⟨p, rfl⟩
    -- this : bimp (lift (Φ p)) p at m = ∀ b ≥ m, Φ p → p b
    exact this m le_rfl hΦ
  later_sExists_false := by
    -- ▷ sExists Φ ⊢ ▷ False ∨ (∃ p, ⌜Φ p⌝ ∧ ▷ p), with later = id:
    -- sExists Φ at m ⊢ or (lift False) (sExists ...) at m
    intro Φ m ⟨p, hΦ, hp⟩
    -- Need: False ∨ ∃ q, (∃ a, and (lift (Φ a)) a = q) ∧ q m
    exact .inr ⟨_, ⟨p, rfl⟩, hΦ, hp⟩
  later_sep := ⟨fun _ hm => hm, fun _ hm => hm⟩
  later_persistently := ⟨fun _ hm => hm, fun _ hm => hm⟩
  later_false_em := by intro _ _ hm; exact .inr (fun _ _ hF => absurd hF id)

/-- Bluebell's Assertion logic is affine: every proposition P satisfies P ⊢ emp.
This is because emp = bident = {a | 1 ≤ a} and OneLe gives 1 ≤ a for all a. -/
instance assertionBIAffine : Iris.BI.BIAffine (Assertion M) where
  affine P := ⟨fun _ _ => one_le _⟩

end BIInstance

end Bluebell
