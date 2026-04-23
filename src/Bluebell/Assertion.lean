import Iris.BI.BIBase
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Set.Basic
import Bluebell.DiscreteCMRA
import Bluebell.MeasureOnSpace
import Iris.Algebra.UPred

open ProbabilityTheory
open MeasureTheory (Measure IsProbabilityMeasure isProbabilityMeasure_iff measure_univ)

namespace Bluebell

variable {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]

abbrev Assertion (M : Type*) [OrderedUnitalResourceAlgebra M] :=
  UpperSet M

@[simp]
abbrev bProp (I Var Val : Type*) [DecidableEq Var] [Inhabited Val] :=
  Assertion (IndexedPSpPm I Var Val)

section ValidIndexedPSpPm

@[simp]
def ValidPSp (Ω : Type*) [Inhabited Ω] : Type _ :=
  {P : PSp Ω // valid P}

@[simp]
def ValidPSp.ms {Ω : Type*} [Inhabited Ω]
  (p : ValidPSp Ω) : MeasurableSpace Ω := by
  obtain ⟨m, hv⟩ := p
  match hcase : m with
  | none => contradiction
  | some m' => exact m'.1.ms

@[simp]
def ValidPSp.μ {Ω : Type*} [Inhabited Ω]
  (p : ValidPSp Ω) : @Measure Ω p.ms := by
  obtain ⟨m, hv⟩ := p
  match hcase : m with
  | none => contradiction
  | some m' => exact m'.1.μ

@[simp]
def ValidPSp.PSpace {Ω : Type*} [Inhabited Ω]
  (p : ValidPSp Ω) : PSpace Ω := by
  obtain ⟨m, hv⟩ := p
  match hcase : m with
  | none => contradiction
  | some m' => exact ⟨⟨m'.1.ms, m'.1.μ⟩, m'.2⟩

@[simp]
def ValidPSpPm (Var Val : Type*) [DecidableEq Var] [Inhabited Val] : Type _ :=
  {P : @PSpPm Var Val _ _ // valid P}

@[simp]
def ValidPSpPm.ms  {Var Val : Type*} [DecidableEq Var] [Inhabited Val]
  (pp : ValidPSpPm Var Val) : MeasurableSpace (Var → Val) := by
  obtain ⟨⟨⟨P, p⟩, h⟩, hv⟩ := pp
  simp [valid] at hv
  letI hP : valid P := by aesop
  letI vP : ValidPSp (Var → Val) := ⟨P, hP⟩
  exact (ValidPSp.ms vP)

@[simp]
def ValidPSpPm.μ  {Var Val : Type*} [DecidableEq Var] [Inhabited Val]
  (pp : ValidPSpPm Var Val) : @Measure (Var → Val) pp.ms := by
  obtain ⟨⟨⟨P, p⟩, h⟩, hv⟩ := pp
  simp [valid] at hv
  letI hP : valid P := by aesop
  letI vP : ValidPSp (Var → Val) := ⟨P, hP⟩
  exact (ValidPSp.μ vP)

@[simp]
def ValidPSpPm.PSpace {Var Val : Type*} [DecidableEq Var] [Inhabited Val]
  (pp : ValidPSpPm Var Val) : PSpace (Var → Val) := by
  obtain ⟨⟨⟨P, p⟩, h⟩, hv⟩ := pp
  simp [valid] at hv
  letI hP : valid P := by aesop
  letI vP : ValidPSp (Var → Val) := ⟨P, hP⟩
  exact (ValidPSp.PSpace vP)

@[simp]
def ValidPSpPm.PSp {Var Val : Type*} [DecidableEq Var] [Inhabited Val]
  (pp : ValidPSpPm Var Val) : PSp (Var → Val) := some (pp.PSpace)

@[simp]
def ValidPSpPm.perm {Var Val : Type*} [DecidableEq Var] [Inhabited Val]
  (pp : ValidPSpPm Var Val) : Permission Var := pp.val.val.2

@[simp]
def ValidIndexedPSpPm (I Var Val : Type*) [DecidableEq Var] [Inhabited Val] : Type _ :=
  {P : IndexedPSpPm I Var Val // valid P}

@[simp]
def ValidIndexedPSpPm.ms {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]
  (m : ValidIndexedPSpPm I Var Val) (i : I) : MeasurableSpace (Var → Val) :=
  ValidPSpPm.ms ⟨m.val i, m.property i⟩

@[simp]
def ValidIndexedPSpPm.μ (m : ValidIndexedPSpPm I Var Val) (i : I)
  : @Measure (Var → Val) (m.ms i) :=
  ValidPSpPm.μ ⟨m.val i, m.property i⟩

@[simp]
def ValidIndexedPSpPm.PSpace (m : ValidIndexedPSpPm I Var Val) (i : I)
  : PSpace (Var → Val) :=
  ValidPSpPm.PSpace ⟨m.val i, m.property i⟩

@[simp]
def ValidIndexedPSpPm.PSp (m : ValidIndexedPSpPm I Var Val) (i : I)
  : PSp (Var → Val) :=
  ValidPSpPm.PSp ⟨m.val i, m.property i⟩

@[simp]
def ValidIndexedPSpPm.perm (m : ValidIndexedPSpPm I Var Val) (i : I)
  : Permission Var :=
  ValidPSpPm.perm ⟨m.val i, m.property i⟩

end ValidIndexedPSpPm

noncomputable section PMF

@[simp]
def PMF.dirac {A : Type*} [Countable A] (x : A) : PMF A :=
  @Measure.toPMF A _ ⊤ _ (@Measure.dirac A ⊤ x) _

notation "δ" => PMF.dirac

@[simp]
def PMF.toDiscMeasure {A : Type*} (μ : PMF A) : @Measure A ⊤ :=
  @μ.toMeasure A ⊤

@[simp]
def PMF.toDiscMeasure_is_probability {A : Type*} (μ : PMF A)
  : IsProbabilityMeasure (PMF.toDiscMeasure μ) := by
  apply isProbabilityMeasure_iff.2
  simp_all only [toDiscMeasure, measure_univ]

instance {A : Type*} : Coe (PMF A) (@Measure A ⊤) where
  coe μ := @μ.toMeasure A ⊤

theorem PMF.dirac_eq_one_iff_eq
  {A : Type*} [Countable A] {x : A} {u : Set A}
  : PMF.toDiscMeasure (PMF.dirac x) u = 1 ↔ x ∈ u := by
  have : (toDiscMeasure (dirac x)) = @Measure.dirac A ⊤ x := by simp
  simp_all only [MeasurableSpace.measurableSet_top, Measure.dirac_apply']
  apply Iff.intro
  · intro a
    by_contra h
    rw [Set.indicator_of_notMem h] at a
    exact zero_ne_one a
  · intro a
    simp_all only [Set.indicator_of_mem, Pi.one_apply]

end PMF

noncomputable section Formula

/-- Allows us to write `P a` instead of `a ∈ P` -/
instance {M : Type*} [OrderedUnitalResourceAlgebra M] : FunLike (Assertion M) M Prop where
  coe := fun P => P.carrier
  coe_injective' := by intro P Q h; aesop

instance : FunLike (bProp I Var Val) (IndexedPSpPm I Var Val) Prop where
  coe := fun P => P.carrier
  coe_injective' := by intro P Q h; aesop

variable {M : Type*} [OrderedUnitalResourceAlgebra M]

def BTrue : Assertion M := {
  carrier := {x | True}
  upper' := by aesop
}

def BFalse : Assertion M := {
  carrier := {x | False}
  upper' := by aesop
}

def lift (φ : Prop) : Assertion M := {
  carrier := {x | φ}
  upper' := by aesop
}

def own (b : M) : Assertion M := {
  carrier := {a | b ≤ a}
  upper' := by
    intro x y h₁ h₂
    have : b ≤ x := by aesop
    have : b ≤ y := by grind
    aesop
}

def and (P Q : Assertion M) : Assertion M := {
  carrier := {a | P a ∧ Q a}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

def or (P Q : Assertion M) : Assertion M := {
  carrier := {a | P a ∨ Q a}
  upper' := by
    intro x y h₁ h₂
    have := P.upper'
    have := Q.upper'
    aesop
}

def sep (P Q : Assertion M) : Assertion M := {
  carrier := {a | ∃ b₁ b₂ : M, (b₁ * b₂) ≤ a ∧ P b₁ ∧ Q b₂}
  upper' := by
    intro a b h₁ h₂
    grind
}

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

def bforall {A : Type*} (K : A → Assertion M) : Assertion M := {
  carrier := {a | ∀ x : A, K x a}
  upper' := by
    intro a b h₁ h₂ x
    have h₃ : ∀ x : A, K x a := by aesop
    have := (K x).upper'
    aesop
}

def entail {ra : OrderedUnitalResourceAlgebra M} (P Q : @Assertion M ra) : Prop :=
  ∀ m, ra.valid m → P m → Q m

def bientail (P Q : Assertion M) : Prop :=
  entail P Q ∧ entail Q P

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

def bpersistently (P : Assertion M) : Assertion M := {
  carrier := {_a | P 1}
  upper' := by intro _ _ _ h; exact h
}

@[simp]
def wand (P Q : Assertion M) : Assertion M := {
  carrier := {a | ∀ b, ✓ (a * b) → P b → Q (a * b)}
  upper' := by
    intro a c hac ha b hvcb hPb
    have hab : a * b ≤ c * b := mul_left_mono hac
    have hvab : ✓ (a * b) := valid_mono hab hvcb
    exact Q.upper' hab (ha b hvab hPb)
}

@[simp]
def bimp (P Q : Assertion M) : Assertion M := {
  carrier := {a | ∀ b, a ≤ b → ✓ b → P b → Q b}
  upper' := by
    intro a c hac ha b hcb hvb hPb
    exact ha b (le_trans hac hcb) hvb hPb
}

@[simp]
def bident : Assertion M := {
  carrier := {a | 1 ≤ a}
  upper' := by
    intro a b hle ha
    simp at *
    apply le_trans <;> aesop
}

section BIInstance

instance : Iris.OFE (bProp I Var Val) := {
  Equiv φ ψ := bientail φ ψ
  Dist _ φ ψ := bientail φ ψ
  dist_eqv := by
    intro n
    constructor
    · intro φ
      constructor <;> exact fun m a a_1 => a_1
    · intro φ ψ h
      exact ⟨h.2, h.1⟩
    · intro φ ψ θ h₁ h₂
      constructor
      · intro m hv hφ
        have := h₁.1 m hv hφ
        have := h₂.1 m hv this
        assumption
      · intro m hv hθ
        have := h₂.2 m hv hθ
        have := h₁.2 m hv this
        assumption
  equiv_dist := ⟨fun h _ => h, fun h => h 0⟩
  dist_lt := by
    intro n x y m h _
    assumption
}

noncomputable instance assertionBIBase : Iris.BI.BIBase (bProp I Var Val) where
  Entails φ ψ := entail φ ψ
  emp := BTrue
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

noncomputable instance assertionBI : Iris.BI (bProp I Var Val) where
  Dist _ φ ψ := bientail φ ψ
  dist_eqv := by
    intro n
    constructor
    · intro φ
      constructor <;> exact fun m a a_1 => a_1
    · intro φ ψ h
      exact ⟨h.2, h.1⟩
    · intro φ ψ θ h₁ h₂
      constructor
      · intro m hv hφ
        have := h₁.1 m hv hφ
        have := h₂.1 m hv this
        assumption
      · intro m hv hθ
        have := h₂.2 m hv hθ
        have := h₁.2 m hv this
        assumption
  equiv_dist := ⟨fun h _ => h, fun h => h 0⟩
  dist_lt := fun h _ => h
  compl := fun h => h 0
  conv_compl := by
    intro n c
    unfold Iris.Chain.chain
    unfold bientail
    have a := @c.cauchy 0 n (zero_le _)
    unfold Iris.OFE.Dist at a
    dsimp at a
    unfold Iris.Chain.chain at a
    constructor
    · exact a.2
    · exact a.1
  Entails φ ψ := entail φ ψ
  emp := BTrue
  pure := lift
  and := and
  or := or
  imp := bimp
  sForall := sForallA
  sExists := sExistsA
  sep := sep
  wand := wand
  persistently := bpersistently
  later := id
  entails_preorder := {
    refl := fun _ _ h => h
    trans := fun h1 h2 m hv hφ => h2 m hv (h1 m hv hφ)
  }
  equiv_iff := by
    intro P Q
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨?_, ?_⟩
      assumption; assumption
    · rintro ⟨h₁, h₂⟩
      refine ⟨?_, ?_⟩
      assumption; assumption
  and_ne := {
    ne := by
      intro _ _ _ hx _ _ hy
      refine ⟨?_, ?_⟩
      · intro m hv ⟨h1, h2⟩
        exact ⟨hx.1 m hv h1, hy.1 m hv h2⟩
      · intro m hv ⟨h1, h2⟩
        exact ⟨hx.2 m hv h1, hy.2 m hv h2⟩
  }
  or_ne := {
    ne := by
      intro _ _ _ hx _ _ hy
      refine ⟨?_, ?_⟩
      · intro m hv h
        rcases h with h1 | h2
        · exact Or.inl (hx.1 m hv h1)
        · exact Or.inr (hy.1 m hv h2)
      · intro m hv h
        rcases h with h1 | h2
        · exact Or.inl (hx.2 m hv h1)
        · exact Or.inr (hy.2 m hv h2)
  }
  imp_ne := {
    ne := by
      intro _ _ _ hx _ _ hy
      refine ⟨?_, ?_⟩
      · intro a _ h b hab hvb hx2b
        exact hy.1 b hvb (h b hab hvb (hx.2 b hvb hx2b))
      · intro a _ h b hab hvb hx1b
        exact hy.2 b hvb (h b hab hvb (hx.1 b hvb hx1b))
  }
  sForall_ne := fun {_ _ _} h => ⟨
    fun m hv hp q hQq =>
      let ⟨p, hPp, heq⟩ := h.2 q hQq
      heq.1 m hv (hp p hPp),
    fun m hv hp p hPp =>
      let ⟨q, hQq, heq⟩ := h.1 p hPp
      heq.2 m hv (hp q hQq)⟩
  sExists_ne := by
    intro n P₁ P₂ h
    refine ⟨?_, ?_⟩
    · intro m hv hex
      obtain ⟨p, hPp, hpm⟩ := hex
      obtain ⟨q, hQq, heq⟩ := h.1 p hPp
      exact ⟨q, hQq, heq.1 m hv hpm⟩
    · intro m hv hex
      obtain ⟨q, hQq, hqm⟩ := hex
      obtain ⟨p, hPp, heq⟩ := h.2 q hQq
      exact ⟨p, hPp, heq.2 m hv hqm⟩
  sep_ne := {
    ne := by
      intro _ _ _ hx _ _ hy
      refine ⟨?_, ?_⟩
      · intro m hv ⟨b₁, b₂, hle, hx1, hy1⟩
        have hv12 := valid_mono hle hv
        have hvb1 := valid_mul hv12
        have hvb2 := valid_mul (by rw [mul_comm] at hv12; exact hv12)
        exact ⟨b₁, b₂, hle, hx.1 b₁ hvb1 hx1, hy.1 b₂ hvb2 hy1⟩
      · intro m hv ⟨b₁, b₂, hle, hx2, hy2⟩
        have hv12 := valid_mono hle hv
        have hvb1 := valid_mul hv12
        have hvb2 := valid_mul (by rw [mul_comm] at hv12; exact hv12)
        exact ⟨b₁, b₂, hle, hx.2 b₁ hvb1 hx2, hy.2 b₂ hvb2 hy2⟩
  }
  wand_ne := {
    ne := by
      intro _ _ _ hx _ _ hy
      refine ⟨?_, ?_⟩
      · intro a _ h b hvab hx2b
        have hvb := valid_mul (by rw [mul_comm] at hvab; exact hvab)
        exact hy.1 _ hvab (h b hvab (hx.2 b hvb hx2b))
      · intro a _ h b hvab hx1b
        have hvb := valid_mul (by rw [mul_comm] at hvab; exact hvab)
        exact hy.2 _ hvab (h b hvab (hx.1 b hvb hx1b))
  }
  persistently_ne := {
    ne := by
      intro _ _ _ hx
      refine ⟨?_, ?_⟩
      · intro _ _ hx1; exact hx.1 1 valid_one hx1
      · intro _ _ hx1; exact hx.2 1 valid_one hx1
  }
  later_ne := {
    ne := fun _ _ _ h => h
  }
  pure_intro := by
    intro _ _ hφ _ _ _
    exact hφ
  pure_elim' := by
    intro _ _ h m hv hφ
    exact h hφ m hv trivial
  and_elim_l := by
    intro _ _ _ _ hPQm
    exact hPQm.1
  and_elim_r := by
    intro _ _ _ _ hPQm
    exact hPQm.2
  and_intro := by
    intro _ _ _ h_PQ h_PR m hv hPm
    exact ⟨h_PQ m hv hPm, h_PR m hv hPm⟩
  or_intro_l := by
    intro _ _ m _ hPm
    exact Or.inl hPm
  or_intro_r := by
    intro _ _ m _ hQm
    exact Or.inr hQm
  or_elim := by
    intro _ _ _ h_PR h_QR m hv hPQm
    rcases hPQm with hPm | hQm
    · exact h_PR m hv hPm
    · exact h_QR m hv hQm
  imp_intro := by
    intro P _ _ h m _ hPm b hmb hvb hQb
    exact h b hvb ⟨P.upper' hmb hPm, hQb⟩
  imp_elim := by
    intro _ _ _ h m hv ⟨hPm, hQm⟩
    exact h m hv hPm m (le_refl m) hv hQm
  sForall_intro := by
    intro _ _ h m hv hPm p hΨp
    exact h p hΨp m hv hPm
  sForall_elim := by
    intro _ p hΨp m _ hf
    exact hf p hΨp
  sExists_intro := by
    intro _ p hΨp m _ hpm
    exact ⟨p, hΨp, hpm⟩
  sExists_elim := by
    intro _ _ h m hv ⟨p, hΦp, hpm⟩
    exact h p hΦp m hv hpm
  sep_mono := by
    intro _ _ _ _ h1 h2 _ hv ⟨b₁, b₂, hle, hP, hP'⟩
    have hv12 : ✓ (b₁ * b₂) := valid_mono hle hv
    have hvb1 : ✓ b₁ := valid_mul hv12
    have hvb2 : ✓ b₂ := valid_mul (by rw [mul_comm] at hv12; exact hv12)
    exact ⟨b₁, b₂, hle, h1 b₁ hvb1 hP, h2 b₂ hvb2 hP'⟩
  emp_sep := by
    intro P
    refine ⟨?_, ?_⟩
    · intro m _ ⟨b₁, b₂, hle, _, hPb₂⟩
      refine P.upper' ?_ hPb₂
      intro i
      refine le_trans ?_ (hle i)
      exact ⟨PSp.le_of_mul_right, by intro x; exact le_add_of_nonneg_left (zero_le _)⟩
    · intro m _ hPm
      exact ⟨1, m, (one_mul m).le, trivial, hPm⟩
  sep_symm := by
    intro _ _ _ _ ⟨b₁, b₂, hle, hP, hQ⟩
    refine ⟨b₂, b₁, ?_, hQ, hP⟩
    rw [mul_comm]; exact hle
  sep_assoc_l := by
    intro _ _ _ _ _ ⟨b₁, b₂, hle, ⟨c₁, c₂, hle', hPc₁, hQc₂⟩, hRb₂⟩
    refine ⟨c₁, c₂ * b₂, ?_, hPc₁, c₂, b₂, le_refl _, hQc₂, hRb₂⟩
    calc c₁ * (c₂ * b₂)
        = (c₁ * c₂) * b₂ := (mul_assoc c₁ c₂ b₂).symm
      _ ≤ b₁ * b₂ := mul_left_mono hle'
      _ ≤ _ := hle
  wand_intro := by
    intro _ _ _ h _ hv hPm b hvmb hQb
    exact h _ hvmb ⟨_, b, le_refl _, hPm, hQb⟩
  wand_elim := by
    intro _ _ R h _ hv ⟨b₁, b₂, hle, hP, hQ⟩
    have hv12 : ✓ (b₁ * b₂) := valid_mono hle hv
    have hvb1 : ✓ b₁ := valid_mul hv12
    exact R.upper' hle (h b₁ hvb1 hP b₂ hv12 hQ)
  persistently_mono := by
    intro _ _ h _ _ hP1
    exact h 1 valid_one hP1
  persistently_idem_2 := by
    intro _ _ _ h
    exact h
  persistently_emp_2 := by
    intro _ _ _
    trivial
  persistently_and_2 := by
    intro _ _ _ _ h
    exact h
  persistently_sExists_1 := by
    intro Ψ _ _ h
    obtain ⟨p, hΨp, hp1⟩ := h
    exact ⟨and (lift (Ψ p)) (bpersistently p), ⟨p, rfl⟩, hΨp, hp1⟩
  persistently_absorb_l := by
    intro _ _ _ _ ⟨_, _, _, hP1, _⟩
    exact hP1
  persistently_and_l := by
    intro _ _ m _ ⟨hP1, hQm⟩
    exact ⟨1, m, (one_mul m).le, hP1, hQm⟩
  later_mono := by
    intro _ _ h
    exact h
  later_intro := by
    intro _ _ _ h
    exact h
  later_sForall_2 := by
    intro Φ m hv h p hΦp
    exact h (bimp (lift (Φ p)) p) ⟨p, rfl⟩ m (le_refl m) hv hΦp
  later_sExists_false := by
    intro Φ _ _ h
    obtain ⟨p, hΦp, hpm⟩ := h
    exact Or.inr ⟨and (lift (Φ p)) p, ⟨p, rfl⟩, hΦp, hpm⟩
  later_sep := by
    intro _ _
    constructor
    · intro _ _ h; exact h
    · intro _ _ h; exact h
  later_persistently := by
    intro _
    constructor
    · intro _ _ h; exact h
    · intro _ _ h; exact h
  later_false_em := by
    intro _ _ _ _
    exact Or.inr (fun _ _ _ hF => hF.elim)

end BIInstance

structure IxCompatiblePermission (P : I → PSp (Var → Val)) where
  perm : I → Permission Var
  comp : ∀ i, (P i).compatiblePerm (perm i)

def ownIndexedPSpPm (P : I → PSp (Var → Val)) (p : IxCompatiblePermission P)
  : bProp I Var Val :=
  iprop(own (fun i ↦ ⟨⟨P i, p.perm i⟩, p.comp i⟩) ∧ ⌜∀ i : I, (P i).isSome⌝)

def ownPSp (P : I → PSp (Var → Val)) : bProp I Var Val :=
  iprop(∃ p : IxCompatiblePermission P, ownIndexedPSpPm P p)

def almostMeasurable {A : Type*} (E : (Var → Val) → A) (P : PSp (Var → Val)) : Prop :=
  match P with
  | none => False
  | some p => @AEMeasurable (Var → Val) A ⊤ _ E p.1.μ

def hasDistribution {A : Type*} (E : (Var → Val) → A) (i : I) (μ : PMF A)
  : bProp I Var Val :=
  iprop(∃ P : ValidIndexedPSpPm I Var Val,
    ownPSp P.PSp ∗
      ⌜let μᵢ := P.μ i
       have Eμᵢ := @μᵢ.map (Var → Val) A (P.ms i) ⊤ E
       almostMeasurable E (P.PSp i)
       ∧ Eμᵢ = @μ.toMeasure A ⊤⌝)

notation:100 E:100 "⟨" i:100 "⟩" " ~ " p:100 => hasDistribution E i p

def almostSurely (E : (Var → Val) → Bool) (i : I) : bProp I Var Val :=
  E⟨i⟩ ~ δ True

notation:100 E:100 "⟨" i:100 "⟩" " = " v:100 => almostSurely (E · = v) i

def ownRV {A : Type*} (E : (Var → Val) → A) (i : I) : bProp I Var Val :=
  iprop(∃ μ : PMF A, E⟨i⟩ ~ μ)

open MeasureTheory in
structure CompatibleKernel (A : Type*) (m : ValidIndexedPSpPm I Var Val) where
  kernel : (i : I) → A → @Measure (Var → Val) (m.ms i)
  isProb : ∀ (i : I) (a : A), IsProbabilityMeasure (kernel i a)
  isComp : ∀ (i : I) (a : A), PSpace.compatiblePerm ⟨⟨m.ms i, kernel i a⟩, isProb i a⟩ (m.perm i)

def jointConditioning {A Var Val : Type*}
  [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
  (μ : PMF A) (K : A → bProp I Var Val)
  : bProp I Var Val :=
  iprop(
    ∃ m : ValidIndexedPSpPm I Var Val,
    ∃ κ : CompatibleKernel A m,
      own m.val
        ∗ (∀ (i : I), ⌜m.μ i = Measure.bind (mα := ⊤) (mβ := m.ms i) μ (κ.kernel i)⌝)
        ∗
          (
            ∀ (v : μ.support),
              (
                own (fun i => ⟨⟨some ⟨⟨m.ms i, κ.kernel i v⟩, κ.isProb i v⟩, m.perm i⟩, κ.isComp i v⟩) -∗
                  (K v))
          )
  )

notation "𝒞" "⟨" μ "⟩" v ";" K => jointConditioning μ (fun v => iprop(K))

def wp {Var Val : Type*}
  [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
  (t : IndexedPSpPm I Var Val → IndexedPSpPm I Var Val)
  (Q : bProp I Var Val) : bProp I Var Val := {
  carrier := fun a =>
    ∀ μ₀ : IndexedPSpPm I Var Val,
      ∀ c : IndexedPSpPm I Var Val,
        ✓ μ₀ → (a * c) ≤ μ₀ → ∃ b : IndexedPSpPm I Var Val,
          (b * c) ≤ t μ₀ ∧ ✓ b ∧ Q b
  upper' := by
    intro x y hxy hx μ₀ c hvμ₀ hmul
    exact hx μ₀ c hvμ₀ (le_trans (mul_left_mono hxy) hmul)
}

def EWPCons
  [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
  (t : IndexedPSpPm I Var Val → IndexedPSpPm I Var Val)
  (Q Q' : bProp I Var Val) (hQ : Q ⊢ Q')
  : wp t Q ⊢ wp t Q' := by
  intro m _ hm μ₀ c hvμ₀ hmul
  obtain ⟨b, hbc, hvb, hQb⟩ := hm μ₀ c hvμ₀ hmul
  exact ⟨b, hbc, hvb, hQ b hvb hQb⟩

def EWPFrame
  [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
  (t : IndexedPSpPm I Var Val → IndexedPSpPm I Var Val)
  (ht : ∀ μ, ✓ μ → ✓ (t μ))
  (P Q : bProp I Var Val)
  : P ∗ wp t Q ⊢ wp t iprop(P ∗ Q) := by
  intro m _ hPwpQ μ₀ c' hvμ₀ hmc'
  obtain ⟨a₁, a₂, hle, hPa₁, hwpQ⟩ := hPwpQ
  have ha₂_le : a₂ * (a₁ * c') ≤ μ₀ :=
    calc a₂ * (a₁ * c')
        = (a₂ * a₁) * c' := (mul_assoc _ _ _).symm
      _ = (a₁ * a₂) * c' := by rw [mul_comm a₂ a₁]
      _ ≤ m * c' := mul_left_mono hle
      _ ≤ μ₀ := hmc'
  obtain ⟨b₀, hb₀c, hvb₀, hQb₀⟩ := hwpQ μ₀ (a₁ * c') hvμ₀ ha₂_le
  have hb_c' : (a₁ * b₀) * c' ≤ t μ₀ :=
    calc (a₁ * b₀) * c'
        = (b₀ * a₁) * c' := by rw [mul_comm a₁ b₀]
      _ = b₀ * (a₁ * c') := mul_assoc _ _ _
      _ ≤ t μ₀ := hb₀c
  have hvab : ✓ (a₁ * b₀) := valid_mul (valid_mono hb_c' (ht μ₀ hvμ₀))
  exact ⟨a₁ * b₀, hb_c', hvab, a₁, b₀, le_refl _, hPa₁, hQb₀⟩

private lemma ValidPSpPm.map_μ_eq_map_PSpace_μ {A : Type*}
    (pp : ValidPSpPm Var Val) (E : (Var → Val) → A) :
    @Measure.map _ _ pp.ms ⊤ E pp.μ = @Measure.map _ _ pp.PSpace.1.ms ⊤ E pp.PSpace.1.μ := by
  obtain ⟨⟨⟨P, perm⟩, hcomp⟩, hv⟩ := pp
  simp [valid] at hv
  cases P with
  | none => exact absurd rfl hv.1
  | some m' => rfl

open MeasureTheory in
theorem EDistInj
  {A : Type*} {E : (Var → Val) → A} {i : I} {μ μ' : PMF A}
  : E⟨i⟩ ~ μ ∧ E⟨i⟩ ~ μ' ⊢ ⌜μ = μ'⌝ := by
  intro m hv h
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨q₁, ⟨P, hq₁P⟩, hq₁m⟩ := h₁
  subst hq₁P
  obtain ⟨b₁, b₂, hle, hown, body⟩ := hq₁m
  obtain ⟨q₁', ⟨p, hq₁'p⟩, hq₁'b₁⟩ := hown
  subst hq₁'p
  obtain ⟨hpown, hsome⟩ := hq₁'b₁
  obtain ⟨q₂, ⟨P', hq₂P'⟩, hq₂m⟩ := h₂
  subst hq₂P'
  obtain ⟨b₁', b₂', hle', hown', body'⟩ := hq₂m
  obtain ⟨q₂', ⟨p', hq₂'p'⟩, hq₂'b₁'⟩ := hown'
  subst hq₂'p'
  obtain ⟨hpown', hsome'⟩ := hq₂'b₁'
  simp only [almostMeasurable, ValidIndexedPSpPm.PSp, ValidPSpPm.PSp] at body body'
  obtain ⟨ham, hμ₁⟩ := body
  obtain ⟨ham', hμ₂⟩ := body'
  have hv_i : valid (m i) := hv i
  have hmi_ne_top : (m i).1.1 ≠ ⊤ := hv_i.1
  match hmi : (m i).1.1 with
  | none => contradiction
  | some y =>
  have hPi_le_m := le_trans (hpown i).1 (le_trans PSp.le_of_mul_left (hle i).1)
  have hP'i_le_m := le_trans (hpown' i).1 (le_trans PSp.le_of_mul_left (hle' i).1)
  rw [hmi] at hPi_le_m hP'i_le_m
  have hxy : P.PSpace i ≤ y := by cases hPi_le_m; assumption
  have hx'y : P'.PSpace i ≤ y := by cases hP'i_le_m; assumption
  have key : @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ
    = @Measure.map _ _ (P'.PSpace i).1.ms ⊤ E (P'.PSpace i).1.μ := by
    apply @Measure.ext _ ⊤
    intro u hu
    simp only [ValidIndexedPSpPm.PSpace] at *
    rw [Measure.map_apply_of_aemeasurable ham hu, Measure.map_apply_of_aemeasurable ham' hu]
    letI : MeasurableSpace A := ⊤
    set f := AEMeasurable.mk E ham
    set f' := AEMeasurable.mk E ham'
    have hf_meas : @Measurable _ _ (P.PSpace i).1.ms ⊤ f := by measurability
    have hf'_meas : @Measurable _ _ (P'.PSpace i).1.ms ⊤ f' := by measurability
    have hf_ae : f =ᵐ[(P.PSpace i).1.μ] E := (AEMeasurable.ae_eq_mk ham).symm
    have hf'_ae : f' =ᵐ[(P'.PSpace i).1.μ] E := (AEMeasurable.ae_eq_mk ham').symm
    have h1 : (P.PSpace i).1.μ (E ⁻¹' u) = (P.PSpace i).1.μ (f ⁻¹' u) :=
      measure_congr (hf_ae.symm.preimage u)
    have h3 : (P'.PSpace i).1.μ (E ⁻¹' u) = (P'.PSpace i).1.μ (f' ⁻¹' u) :=
      measure_congr (hf'_ae.symm.preimage u)
    have h2 : (P.PSpace i).1.μ (f ⁻¹' u) = y.1.μ (f ⁻¹' u) :=
      MeasureOnSpace.le_preserves_measure hxy (hf_meas hu)
    have h4 : (P'.PSpace i).1.μ (f' ⁻¹' u) = y.1.μ (f' ⁻¹' u) :=
      MeasureOnSpace.le_preserves_measure hx'y (hf'_meas hu)
    have extend_ae : ∀ {g : (Var → Val) → A} {z : PSpace (Var → Val)}
      (hzy : z ≤ y) (_ : g =ᵐ[z.1.μ] E), g =ᵐ[y.1.μ] E := by
      intro g z hzy hg_ae
      rw [Filter.EventuallyEq, ae_iff] at hg_ae
      rcases @exists_measurable_superset_of_null _ z.1.ms z.1.μ _ hg_ae
        with ⟨N, hN_sub, hN_meas, hN_null⟩
      have hN_y : y.1.μ N = 0 := by
        rw [← hN_null]; exact (MeasureOnSpace.le_preserves_measure hzy hN_meas).symm
      exact measure_mono_null hN_sub hN_y
    have hff'_ae : f =ᵐ[y.1.μ] f' :=
      (extend_ae hxy hf_ae).trans (extend_ae hx'y hf'_ae).symm
    have h5 : y.1.μ (f ⁻¹' u) = y.1.μ (f' ⁻¹' u) :=
      measure_congr (hff'_ae.preimage u)
    change (P.PSpace i).1.μ (E ⁻¹' u) = (P'.PSpace i).1.μ (E ⁻¹' u)
    rw [h1, h2, h5, ← h4, ← h3]
  show μ = μ'
  apply @PMF.toMeasure_injective A ⊤
  have bridge : ∀ (Q : ValidIndexedPSpPm I Var Val),
      @Measure.map _ _ (Q.ms i) ⊤ E (Q.μ i)
      = @Measure.map _ _ (Q.PSpace i).1.ms ⊤ E (Q.PSpace i).1.μ := by
    intro Q
    obtain ⟨Qval, Qprop⟩ := Q
    have hv_Q := Qprop i
    rcases hQi : Qval i with ⟨⟨P_, perm_⟩, hcomp⟩
    simp only [hQi, valid] at hv_Q
    cases hP_ : P_ with
    | none => subst hP_; exact absurd rfl hv_Q.1
    | some m' =>
      subst hP_
      exact ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨Qval i, Qprop i⟩ E
  calc @PMF.toMeasure A ⊤ μ
      = @Measure.map _ _ (P.ms i) ⊤ E (P.μ i) := hμ₁.symm
    _ = @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ := bridge P
    _ = @Measure.map _ _ (P'.PSpace i).1.ms ⊤ E (P'.PSpace i).1.μ := key
    _ = @Measure.map _ _ (P'.ms i) ⊤ E (P'.μ i) := (bridge P').symm
    _ = @PMF.toMeasure A ⊤ μ' := hμ₂

theorem ESureDirac
  {A : Type*} [Countable A] [DecidableEq A] {E : (Var → Val) → A} {i : I} {v : A}
  : E⟨i⟩ ~ δ v ⊣⊢ E⟨i⟩ = v := by
  constructor
  · intro m hv h
    obtain ⟨q, ⟨P, hqP⟩, hqm⟩ := h
    subst hqP
    obtain ⟨b₁, b₂, hle, hown, body⟩ := hqm
    refine ⟨_, ⟨P, rfl⟩, b₁, b₂, hle, hown, ?_⟩
    simp only [almostMeasurable, ValidIndexedPSpPm.PSp, ValidPSpPm.PSp] at body ⊢
    obtain ⟨ham, hμ⟩ := body
    obtain ⟨E', hE'_meas, hE'_ae⟩ := ham
    letI : MeasurableSpace A := ⊤
    have hg : @Measurable A Bool ⊤ ⊤ (fun a => decide (a = v)) := fun _ _ => trivial
    have bridge_E : @Measure.map _ _ (P.ms i) ⊤ E (P.μ i)
        = @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ :=
      ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ E
    rw [bridge_E] at hμ
    constructor
    · refine ⟨(fun a => decide (a = v)) ∘ E', hg.comp hE'_meas, ?_⟩
      exact hE'_ae.fun_comp (fun a => decide (a = v))
    · have bridge_dec : @Measure.map _ _ (P.ms i) ⊤ (fun x => decide (E x = v)) (P.μ i)
          = @Measure.map _ _ (P.PSpace i).1.ms ⊤ (fun x => decide (E x = v))
              (P.PSpace i).1.μ :=
        ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ _
      rw [bridge_dec]
      apply @Measure.ext _ ⊤
      intro s hs
      have ham_E : AEMeasurable E (P.PSpace i).1.μ := ⟨E', hE'_meas, hE'_ae⟩
      have ham_c : AEMeasurable (fun x => decide (E x = v)) (P.PSpace i).1.μ := by
        refine ⟨(fun a => decide (a = v)) ∘ E', hg.comp hE'_meas, ?_⟩
        exact hE'_ae.fun_comp (fun a => decide (a = v))
      rw [Measure.map_apply_of_aemeasurable (mβ := ⊤) ham_c hs]
      change (P.PSpace i).1.μ (E ⁻¹' ((fun a => decide (a = v)) ⁻¹' s)) = _
      rw [← Measure.map_apply_of_aemeasurable (mβ := ⊤) ham_E
            MeasurableSpace.measurableSet_top, hμ]
      change PMF.toDiscMeasure (δ v) _ = PMF.toDiscMeasure (δ (decide True)) _
      simp only [PMF.dirac, PMF.toDiscMeasure, Measure.toPMF_toMeasure,
        Measure.dirac_apply', MeasurableSpace.measurableSet_top]
      classical
      simp [Set.indicator_apply, Set.mem_preimage]
  · intro m hv h
    obtain ⟨q, ⟨P, hqP⟩, hqm⟩ := h
    subst hqP
    obtain ⟨b₁, b₂, hle, hown, body⟩ := hqm
    refine ⟨_, ⟨P, rfl⟩, b₁, b₂, hle, hown, ?_⟩
    simp only [almostMeasurable, ValidIndexedPSpPm.PSp, ValidPSpPm.PSp] at body
    obtain ⟨ham, hμ⟩ := body
    letI : MeasurableSpace A := ⊤
    have bridge_dec : @Measure.map _ _ (P.ms i) ⊤ (fun x => decide (E x = v)) (P.μ i)
        = @Measure.map _ _ (P.PSpace i).1.ms ⊤ (fun x => decide (E x = v))
            (P.PSpace i).1.μ :=
      ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ _
    rw [bridge_dec] at hμ
    simp only [ValidIndexedPSpPm.PSpace] at hμ
    have h_null : (P.PSpace i).1.μ {s | ¬ E s = v} = 0 := by
      have h1 := Measure.map_apply_of_aemeasurable ham (s := {false}) MeasurableSpace.measurableSet_top
      rw [hμ] at h1
      simp only [PMF.dirac, Measure.toPMF_toMeasure,
        MeasurableSpace.measurableSet_top, Measure.dirac_apply'] at h1
      classical
      simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply] at h1
      rw [show (P.PSpace i).1.μ {s | ¬E s = v}
          = (P.PSpace i).1.μ ((fun x => decide (E x = v)) ⁻¹' {false}) from by
        congr 1; ext x; simp [Set.mem_preimage, decide_eq_false_iff_not]]
      exact h1.symm
    have hae : E =ᵐ[_] (fun _ => v) := h_null
    simp only [ValidIndexedPSpPm.PSpace] at hae
    have bridge_E : @Measure.map _ _ (P.ms i) ⊤ E (P.μ i)
        = @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ :=
      ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ E
    constructor
    · exact ⟨fun _ => v, measurable_const, hae⟩
    · rw [bridge_E]; simp only [ValidIndexedPSpPm.PSpace]
      rw [Measure.map_congr (mβ := ⊤) hae]
      apply @Measure.ext _ ⊤
      intro s hs
      rw [Measure.map_apply_of_aemeasurable (mβ := ⊤) measurable_const.aemeasurable hs]
      classical
      by_cases hv_s : v ∈ s
      · rw [Set.preimage_const_of_mem hv_s]
        exact ((ValidPSpPm.PSpace ⟨P.val i, P.property i⟩).2.measure_univ).trans
          (by simp [PMF.dirac, Measure.toPMF_toMeasure,
                Measure.dirac_apply_of_mem hv_s])
      · rw [Set.preimage_const_of_notMem hv_s, MeasureTheory.measure_empty]
        simp only [PMF.dirac, Measure.toPMF_toMeasure, Measure.dirac_apply', MeasurableSpace.measurableSet_top]
        exact (Set.indicator_of_notMem hv_s _).symm

theorem EDiracDup
  {A : Type*} [Countable A]
  {E : (Var → Val) → A} (i : I) (v : A)
  :   E⟨i⟩ ~ δ v
    ⊢ E⟨i⟩ ~ δ v ∗ E⟨i⟩ ~ δ v := by
  sorry

theorem ESureMerge
  {A : Type*}
  {E₁ E₂ : (Var → Val) → Bool} {i : I}
  : E₁⟨i⟩ = true ∗ E₂⟨i⟩ = true ⊣⊢ (fun s => E₁ s ∧ E₂ s)⟨i⟩ = true := by
  sorry

end Formula

section Properties

theorem and_ident {P : bProp I Var Val}
  : P ∧ BTrue ⊣⊢ P := by
  constructor
  · intro m _ hm
    exact hm.1
  · intro m _ hm
    exact ⟨hm, trivial⟩

theorem and_comm {P Q : bProp I Var Val}
  : P ∧ Q ⊣⊢ Q ∧ P := by
  constructor
  · intro m _ hm
    exact ⟨hm.2, hm.1⟩
  · intro m _ hm
    exact ⟨hm.2, hm.1⟩

theorem and_assoc {P Q R : bProp I Var Val}
  : (P ∧ Q) ∧ R ⊣⊢ P ∧ (Q ∧ R) := by
  constructor
  · intro m _ hm
    exact ⟨hm.1.1, hm.1.2, hm.2⟩
  · intro m _ hm
    exact ⟨⟨hm.1, hm.2.1⟩, hm.2.2⟩

theorem or_ident {P : bProp I Var Val}
  : P ∨ BFalse ⊣⊢ P := by
  constructor
  · intro m _ hm
    rcases hm with hP | hF
    · exact hP
    · exact hF.elim
  · intro m _ hm
    exact Or.inl hm

theorem or_comm {P Q : bProp I Var Val}
  : P ∨ Q ⊣⊢ Q ∨ P := by
  constructor
  · intro m _ hm
    exact hm.symm
  · intro m _ hm
    exact hm.symm

theorem or_assoc {P Q R : bProp I Var Val}
  : (P ∨ Q) ∨ R ⊣⊢ P ∨ (Q ∨ R) := by
  constructor
  · intro m _ hm
    rcases hm with (hP | hQ) | hR
    · exact Or.inl hP
    · exact Or.inr (Or.inl hQ)
    · exact Or.inr (Or.inr hR)
  · intro m _ hm
    rcases hm with hP | hQ | hR
    · exact Or.inl (Or.inl hP)
    · exact Or.inl (Or.inr hQ)
    · exact Or.inr hR

theorem sep_ident {P : bProp I Var Val}
  : P ∗ True ⊣⊢ P := by
  refine ⟨?_, ?_⟩
  · intro m _ hm
    obtain ⟨b₁, b₂, hle, hPb₁, _⟩ := hm
    refine P.upper' ?_ hPb₁
    intro i
    refine le_trans ?_ (hle i)
    refine ⟨PSp.le_of_mul_left, ?_⟩
    intro x
    exact le_add_of_nonneg_right (zero_le _)
  · intro m _ hm
    exact ⟨m, 1, (mul_one m).le, hm, trivial⟩

theorem sep_comm {P Q : bProp I Var Val}
  : P ∗ Q ⊣⊢ Q ∗ P := by
  constructor
  · intro m hv hm
    obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
    use b₂, b₁
    have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
    aesop
  · intro m hv hm
    obtain ⟨b₁, ⟨b₂, h⟩⟩ := hm
    use b₂, b₁
    have : b₁ * b₂ = b₂ * b₁ := CommMonoid.mul_comm b₁ b₂
    aesop

theorem sep_assoc {P Q R : bProp I Var Val}
  : (P ∗ Q) ∗ R ⊣⊢ P ∗ (Q ∗ R) := by
  constructor
  · intro m _ hm
    obtain ⟨b₁, b₂, hle, ⟨c₁, c₂, hle', hPc₁, hQc₂⟩, hRb₂⟩ := hm
    refine ⟨c₁, c₂ * b₂, ?_, hPc₁, c₂, b₂, le_refl _, hQc₂, hRb₂⟩
    calc c₁ * (c₂ * b₂)
        = (c₁ * c₂) * b₂ := (mul_assoc c₁ c₂ b₂).symm
      _ ≤ b₁ * b₂ := mul_left_mono hle'
      _ ≤ m := hle
  · intro m _ hm
    obtain ⟨b₁, b₂, hle, hPb₁, ⟨c₁, c₂, hle', hQc₁, hRc₂⟩⟩ := hm
    refine ⟨b₁ * c₁, c₂, ?_, ⟨b₁, c₁, le_refl _, hPb₁, hQc₁⟩, hRc₂⟩
    calc (b₁ * c₁) * c₂
        = b₁ * (c₁ * c₂) := mul_assoc b₁ c₁ c₂
      _ ≤ b₁ * b₂ := by
          rw [mul_comm b₁ (c₁ * c₂), mul_comm b₁ b₂]
          exact mul_left_mono hle'
      _ ≤ m := hle

variable [Finite Var] [Countable Val]

example {P : bProp I Var Val} : ⊢ P -∗ BTrue := by
  exact Iris.BI.entails_wand fun m a a_1 => trivial

omit [Finite Var] [Countable Val]
lemma emp_implies_own_unit : emp ⊢ own (1 : IndexedPSpPm I Var Val) := by
  intro m hv hemp
  have : m ∈ {a | 1 ≤ a} := by
    have : 1 ≤ m := IndexedPSpPm.one_le I Val Var
    aesop
  assumption

lemma true_subst_star
  {P Q : bProp I Var Val} (h : Q ⊣⊢ BTrue)
  : P ⊢ P ∗ Q := by
  intro m hv hp
  simp [Iris.BI.sep]
  have : m ∈ sep P Q := by
    simp [Membership.mem, Set.Mem, sep]
    use m, 1
    have : Q 1 := by
      have : 1 ∈ (BTrue : bProp I Var Val) := by
        simp [Membership.mem, Set.Mem, BTrue]
        trivial
      have := h.2 1 (by aesop) this
      assumption
    constructor
    · have : m * 1 = m := MulOneClass.mul_one m
      rw [this]
    · exact ⟨hp, by assumption⟩
  assumption

noncomputable instance : OfNat (ValidIndexedPSpPm I Var Val) 1 where
  ofNat := ⟨1, by aesop⟩

noncomputable def validOne : ValidIndexedPSpPm I Var Val := 1

noncomputable def k {A : Type*} : CompatibleKernel A (@validOne I Var Val _ _) := {
  kernel := fun i _ => PSpace.unit.1.μ
  isProb := fun i a => by
    have := (@validOne.PSpace I Var Val _ _ i).2
    assumption
  isComp := by
    intro i a
    cases h : (@validOne I Var Val _ _).1 i
    obtain ⟨p, h⟩ := h
    aesop
}

lemma step_one : (BTrue : bProp I Var Val) ⊢ own (validOne.val : IndexedPSpPm I Var Val) := by
  intro m hv ht
  simp [own]
  have : validOne.val = (1 : IndexedPSpPm I Var Val) := by rfl
  rw [this]
  have : m ∈ own 1 := by
    simp [Membership.mem, Set.Mem, own]
    assumption
  assumption

noncomputable abbrev ASSERTION_TWO {A : Type*} (μ : PMF A) : bProp I Var Val :=
  iprop(⌜∀ i : I, (validOne.μ i : @Measure (Var → Val) (validOne.ms i))
    = Measure.bind (α := A) (mα := ⊤) (mβ := validOne.ms i) μ (k.kernel i)⌝)

lemma second_trivial {A : Type*} (μ : PMF A)
  : ⊢ (ASSERTION_TWO μ : bProp I Var Val) := by
  intro m _ _ i
  let o := validOne (I := I) (Var := Var) (Val := Val)
  have : o.μ i = Measure.bind (α := A) (mα := ⊤) μ (@k.kernel (Var := Var) (Val := Val) i) := by
    have : o.μ i = PSpace.unit.1.μ := by rfl
    rw [this]
    have : (k.kernel (A := A) (Var := Var) (Val := Val) i) =
      fun _ => (PSpace.unit.1.μ : @Measure (Var → Val) (validOne.ms i)) := by rfl
    rw [this, MeasureTheory.Measure.bind_const]
    aesop
  rw [this]

lemma step_two {A : Type*} (μ : PMF A) :
  own (1 : IndexedPSpPm I Var Val)
    ⊢ own (1 : IndexedPSpPm I Var Val) ∗ ASSERTION_TWO μ := by
  apply true_subst_star
  constructor
  · intro m hv ha
    have : m ∈ BTrue := by trivial
    assumption
  · have := @second_trivial I Var Val _ _ A μ
    assumption

noncomputable abbrev ASSERTION_THREE
  {A : Type*} (μ : PMF A) : bProp I Var Val :=
  iprop(∀ (_v : μ.support), own validOne.val -∗ BTrue)

lemma step_three {A : Type*} (μ : PMF A)
  :   own (1 : IndexedPSpPm I Var Val) ∗ ASSERTION_TWO μ
    ⊢ own (1 : IndexedPSpPm I Var Val) ∗ ASSERTION_TWO μ ∗ BTrue
  := by
  intro m hv hp
  apply true_subst_star
  constructor
  · intro m hv hp; trivial
  · intro m hm hp
    have := @second_trivial I Var Val _ _ A μ
    have : m ∈ iprop(ASSERTION_TWO μ ∗ BTrue) := by
      show m ∈ (sep (ASSERTION_TWO μ) BTrue)
      simp [sep]
      use m, 1
      constructor <;> aesop
    assumption
  assumption
  have h := @step_one I Var Val _ _
  have := h m hv (by trivial)
  aesop

noncomputable abbrev ASSERTION_FOUR
  {A : Type*} (μ : PMF A) : bProp I Var Val :=
  iprop(
    ∃ m : ValidIndexedPSpPm I Var Val,
    ∃ κ : CompatibleKernel A m,
      own m.val
        ∗ ASSERTION_TWO μ
        ∗ ASSERTION_THREE μ
  )

lemma step_four
  {A : Type*} (μ : PMF A) :
  (own (1 : IndexedPSpPm I Var Val) ∗ ASSERTION_TWO μ ∗ ASSERTION_THREE μ : bProp I Var Val)
    ⊢ ASSERTION_FOUR μ
  := by
  intro a hv hp
  simp [ASSERTION_THREE] at hp
  unfold ASSERTION_FOUR
  have : a ∈ iprop(∃ (m : ValidIndexedPSpPm I Var Val) (k : CompatibleKernel A m),
    own m.val ∗ ASSERTION_TWO μ ∗ ASSERTION_THREE μ) := by
    simp [Membership.mem, Set.Mem]
    have : a ∈ iprop(own validOne.val ∗ ASSERTION_TWO μ ∗ ASSERTION_THREE μ) := by sorry
    simp [Iris.BI.exists, Iris.BI.sExists, sExistsA]
    apply Set.mem_setOf.2
    use validOne.val
    use (@validOne I Var Val _ _).property
    constructor
    · constructor
      exact k
    · assumption
  assumption

noncomputable abbrev ASSERTION_FIVE
  {A : Type*} (μ : PMF A) : bProp I Var Val :=
  𝒞⟨μ⟩ _v; BTrue

lemma step_five
  {I Var Val : Type*} [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
  {A : Type*} (μ : PMF A)
  : (ASSERTION_FOUR μ : bProp I Var Val) ⊢ ASSERTION_FIVE μ := by
  intro a hv hp
  unfold ASSERTION_FOUR at hp
  unfold ASSERTION_FIVE
  have : a ∈ ASSERTION_FIVE μ := by
    unfold ASSERTION_FIVE
    simp [jointConditioning]
    apply Set.mem_setOf.2

    sorry
  assumption

omit [Finite Var] [Countable Val] in
lemma lem1 {P : bProp I Var Val} : P ⊢ P ∗ BTrue := by
  have : (BTrue : bProp I Var Val) = iprop(emp) := by rfl
  rw [this]
  -- A * B ∧ B -∗ C ⊢ A * C
  exact Iris.ProofMode.from_and_intro (fun m a a_1 => a_1) fun m a a_1 => trivial

-- instance : OfNat (CompatibleKernel A 1) 1 := _

#check jointConditioning

lemma C_True
  {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]
  [Finite Var] [Countable Val] {A : Type} {μ : PMF A}
  : ⊢ (𝒞⟨μ⟩ v; BTrue : bProp I Var Val) := by
  intro m hv hemp
  unfold jointConditioning
  simp [Iris.BI.exists, Iris.BI.sExists, sExistsA]
  use validOne.val
  use (@validOne I Var Val _ _).property
  constructor
  · use m, validOne.val
    constructor
    · show m * 1 ≤ m
      simp_all only [bProp, PSp.compatiblePerm, mul_one, le_refl]
    · constructor
      · sorry
      · use validOne.val, validOne.val
        constructor
        · show 1 * 1 ≤ 1; simp
        · simp_all only [bProp, PSp.compatiblePerm, OrderedUnitalResourceAlgebra.instValidForall.eq_1]
          apply And.intro
          · simp [Iris.BI.forall, Iris.BI.sForall, sForallA]
            intro i
            simp [Iris.BI.pure, lift]
            let o : PSp (Var → Val) := ((@validOne I Var Val _ _).1 i).1.1
            have : o = some 1 := by rfl
            have ho : valid o := by
              simp_all only [bProp, PSp.compatiblePerm, OrderedUnitalResourceAlgebra.instValidForall.eq_1, o]
              sorry
            aesop
            sorry
          · simp [Iris.BI.forall, Iris.BI.sForall, sForallA]
            intro p u x h
            sorry
  · exact k

end Properties

end Bluebell
