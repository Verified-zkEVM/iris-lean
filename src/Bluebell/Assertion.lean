import Iris.BI.BIBase
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Bluebell.DiscreteCMRA
import Bluebell.MeasureOnSpace
import Iris.BI.BIBase
import Iris.Algebra.UPred

open MeasureTheory

namespace Bluebell

variable {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]

abbrev Assertion (M : Type*) [OrderedUnitalResourceAlgebra M] :=
  UpperSet M

section Formula

#check Iris.UPred

-- (F, μ) ≤bb (G, ν) <=> F ⊆ G ∧ ν|F = μ
-- (F, μ) ≤iris (G, ν) <=> ∃(H, ρ), (G, ν) = (F, μ) * (H, ρ)

-- iris => bb
--   G = σ{F ∪ H}
--   (1) : ∀ U in F, V in H, ν(U ∩ V) = μ(U) * ρ(V).
--   ν|F = μ <=> ∀ U in F, μ(U) = ν(U)
--   from (1), set U := U, V := Univ, ν(U) = μ(U)

-- bb =/=> iris
-- choose H := G
--

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

notation:30 "⊢ " P => entail BTrue P
notation:30 P " ⊢ " Q => entail P Q
notation:30 P " ⊣⊢ " Q => bientail P Q
notation:40 "∀'" K => bforall K
notation:40 "∃'" K => bexists K
notation:50 "⌈" φ "⌉" => lift φ
notation:60 P " ∧' " Q => and P Q
notation:60 P " ∨' " Q => or P Q
notation:70 P:70 " *' " Q:71 => sep P Q

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

@[simp]
def isDistributed {A : Type*} [MeasurableSpace A] (E : (Var → Val) → A) (μ : Measure A)
  : Assertion (IndexedPSpPm I Var Val) :=
  bexists (fun P : I → PSp (Var → Val) =>
    ownPSp P *' lift (
      μ = (P i).1.μ.toPMF.map (E i)
      ∧ sorry
    )
  )

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

end Properties

end Bluebell
