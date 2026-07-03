import Iris.Algebra.UPred
import Iris.BI.BIBase
import Bluebell.MeasureOnSpace
import Bluebell.OURA
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Order.SetNotation
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions

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

def product {A B : Type*} (μ₁ : PMF A) (μ₂ : PMF B) : PMF (A × B) :=
  let prf : HasSum (fun (a, b) => μ₁ a * μ₂ b) 1 := (by
      have h : ∑' (p : A × B), μ₁ p.1 * μ₂ p.2 = 1 := by
        simp_rw [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          PMF.tsum_coe, mul_one]
      convert h ▸ ENNReal.summable.hasSum)
  ⟨fun ((a, b) : (A × B)) => μ₁ a * μ₂ b, prf⟩

notation μ₁ "⊗" μ₂ => product μ₁ μ₂

instance {A : Type*} : Coe (PMF A) (@Measure A ⊤) where
  coe μ := @μ.toMeasure A ⊤

theorem PMF.dirac_eq_one_iff_eq
  {A : Type*} [Countable A] {x : A} {u : Set A}
  : PMF.toDiscMeasure (PMF.dirac x) u = 1 ↔ x ∈ u := by
  have : (toDiscMeasure (dirac x)) = @Measure.dirac A ⊤ x := by simp only [toDiscMeasure, dirac,
    Measure.toPMF_toMeasure]
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

-- ⊢ {P} C {Q} -- ⊢ {P} [0: C_0, 1: C_1] {Q}

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

instance : Iris.BI.Persistent (BTrue : bProp I Var Val) where
  persistent := Iris.BI.BIBase.Entails.rfl

instance {P : bProp I Var Val} : Iris.BI.Affine P where
  affine := fun _ _ _ ↦ trivial

instance {P : bProp I Var Val} : Iris.BI.Absorbing P where
  absorbing := by
    unfold Iris.BI.absorbingly
    iintro ⟨_, h⟩
    iexact h

instance {P : bProp I Var Val} : Iris.BI.Timeless P where
  timeless := by
    change P ⊢ False ∨ P
    iintro h
    iright
    iexact h


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

def almostSurely (E : (Var → Val) → Prop) (i : I) : bProp I Var Val :=
  E⟨i⟩ ~ δ True

notation "⌈" E:105 "⟨" i "⟩⌉" => almostSurely E i

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
        ∧ (∀ (i : I), ⌜m.μ i = Measure.bind (mα := ⊤) (mβ := m.ms i) μ (κ.kernel i)⌝)
        ∧ (∀ (v : μ.support), ⌜(fun i => ⟨⟨some ⟨⟨m.ms i, κ.kernel i v⟩, κ.isProb i v⟩, m.perm i⟩, κ.isComp i v⟩) ∈ (K v).carrier⌝
  ))

notation "𝒞" "⟨" μ "⟩" v ";" K:45 => jointConditioning μ (fun v => iprop(K))

def hyperTermSemantics {Var Val : Type*} [DecidableEq Var] [Inhabited Val]
      (t : I → Option ((PSpPm Var Val) → (PSpPm Var Val)))
      (μ : IndexedPSpPm I Var Val)
  : IndexedPSpPm I Var Val :=
  fun (i : I) =>
    match t i with
    | .some t_i => t_i (μ i)
    | .none => μ i

notation "⟦" t "⟧" μ => hyperTermSemantics t μ

def hyperTermReferences (t : I → Option (PSpPm Var Val → PSpPm Var Val)) : Set I :=
  {x | (t x).isSome}

/-- Short for "domain" -/
abbrev dom (t : I → Option (PSpPm Var Val → PSpPm Var Val)) := hyperTermReferences t

def wp {Var Val : Type*}
  [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
  (t : I → Option (PSpPm Var Val → PSpPm Var Val))
  (Q : bProp I Var Val) : bProp I Var Val := {
  carrier := fun a =>
    ∀ μ₀ : IndexedPSpPm I Var Val,
      ∀ c : IndexedPSpPm I Var Val,
        ✓ μ₀ → (a * c) ≤ μ₀ → ∃ b : IndexedPSpPm I Var Val,
          (b * c) ≤ (⟦t⟧ μ₀) ∧ ✓ b ∧ Q b
  upper' := by
    intro x y hxy hx μ₀ c hvμ₀ hmul
    exact hx μ₀ c hvμ₀ (le_trans (mul_left_mono hxy) hmul)
}

def hoare {Var Val : Type*}
  [DecidableEq Var] [Inhabited Val] [Finite Var] [Countable Val]
  (P : bProp I Var Val)
  (t : I → Option (PSpPm Var Val → PSpPm Var Val))
  (Q : bProp I Var Val) : bProp I Var Val :=
  bpersistently (wand P (@wp I Var Val _ _ _ _ t Q))

notation:100 "{" P "} " t "{" Q "}" => hoare P t Q

private lemma ValidPSpPm.map_μ_eq_map_PSpace_μ {A : Type*}
    (pp : ValidPSpPm Var Val) (E : (Var → Val) → A) :
    @Measure.map _ _ pp.ms ⊤ E pp.μ = @Measure.map _ _ pp.PSpace.1.ms ⊤ E pp.PSpace.1.μ := by
  obtain ⟨⟨⟨P, perm⟩, hcomp⟩, hv⟩ := pp
  simp [valid] at hv
  cases P with
  | none => exact absurd rfl hv.1
  | some m' => rfl

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
  · iintro ⟨h, _⟩
    iexact h
  · iintro h
    isplitl [h]
    · iexact h
    · exact fun m a a_1 => a_1

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


lemma sep_affine
  {P Q : bProp I Var Val}
  : P ∗ Q ⊢ P := by
  iintro ⟨h1, h2⟩
  iexact h1

end Properties

section BluebellRules

-- # Additional definitions used in Bluebell rules

variable [Finite Var] [Countable Val]

/-
🤖: The product distribution `μ₁ ⊗ μ₂` is the iterated `bind`.
-/
private lemma product_eq_bind {A B : Type*} (μ₁ : PMF A) (μ₂ : PMF B) :
    (μ₁ ⊗ μ₂) = PMF.bind μ₁ (fun a => PMF.bind μ₂ (fun b => PMF.pure (a, b))) := by
  ext ⟨a, b⟩; simp [PMF.bind_apply, PMF.pure_apply];
  erw [ tsum_eq_single a ];
  · rw [ tsum_eq_single b ] ; aesop;
    grind;
  · aesop

/-- `irrel` from p17 of the Bluebell paper -/
def irrelevant
  (J : Set I) (P : bProp I Var Val) :=
    ∀ a : (I → (PSpPm Var Val)),
      (∃ (a' : (I → (PSpPm Var Val))), valid a'
                                      ∧ (∀ (i : I), i ∉ J → a i = a' i)
                                      ∧ P a')
      → P a

/-- `idx` from p17 of the Bluebell paper -/
def idx
  (P : bProp I Var Val) : Set I :=
    ⋂₀ {J : Set I | irrelevant {i:I | i ∉ J} P} -- Intersection of all sets satisfying a property is the smallest subset satisfying it.

-- For SURE-AND-STAR and RL-SURE-MERGE
def pvar {A : Type*} (E : (Var → Val) → A) : Set Var :=
  {x : Var | ∃ (σ : Var → Val) (v : Val), E σ ≠ E (Function.update σ x v)}

-- For SURE-AND-STAR
-- The `PSpace.compatiblePerm` predicate only constrains a permission's behaviour on its
-- zero-valued (`Irr`) variables, so swapping the value at a single variable for any nonzero
-- value preserves compatibility.
omit [Finite Var] [Countable Val] [Inhabited Val] in
private lemma compatiblePerm_update_update_of_ne_zero [DecidableEq I]
    {P : PSpace (Var → Val)} {p : I → Permission Var} {v : I × Var}
    {a b : ℚ≥0} (hb : b ≠ 0) {i : I}
    (h : PSpace.compatiblePerm P
          (Function.update p v.1 (Function.update (p v.1) v.2 a) i)) :
    PSpace.compatiblePerm P
      (Function.update p v.1 (Function.update (p v.1) v.2 b) i) := by
  intro u hu s hs x hx v_val
  apply h u hu s hs x ?_ v_val
  simp only [Irr, Set.mem_setOf_eq] at hx ⊢
  by_cases hi : i = v.1
  · subst hi
    rw [Function.update_self] at hx ⊢
    by_cases hxv : x = v.2
    · subst hxv
      rw [Function.update_self] at hx
      exact absurd hx hb
    · rw [Function.update_of_ne hxv] at hx ⊢
      exact hx
  · rw [Function.update_of_ne hi] at hx ⊢
    exact hx

-- For SURE-AND-STAR
def pabs [DecidableEq I] (P : bProp I Var Val) (X : Set (I × Var)) : Prop :=
  ∀ v ∈ X,
  ∀ ℱ : I → MeasurableSpace (Var → Val),
  ∀ μ : (i : I) → @Measure (Var → Val) (ℱ i),
  ∀ mu_compat : (i : I) → IsProbabilityMeasure (μ i),
  ∀ p : I → Permission Var,
  ∀ q n : ℕ+,
  ∀ p_compat : (i : I) → PSpace.compatiblePerm
      ⟨{ ms := ℱ i, μ := μ i }, mu_compat i⟩
      (Function.update p v.1 (Function.update (p v.1) v.2 q.1) i),
  (fun i ↦
    ⟨⟨.some ⟨⟨ℱ i, μ i⟩, mu_compat i⟩,
        Function.update p v.1 (Function.update (p v.1) v.2 q.1) i⟩,
      by simp only [PSp.compatiblePerm]; exact p_compat i⟩) ∈ P →
  (fun i ↦
    ⟨⟨.some ⟨⟨ℱ i, μ i⟩, mu_compat i⟩,
        Function.update p v.1 (Function.update (p v.1) v.2
          ⟨mkRat q.1 n.1, Rat.mkRat_nonneg (Int.natCast_nonneg ↑q) ↑n⟩) i⟩,
      by
        simp only [PSp.compatiblePerm]
        refine compatiblePerm_update_update_of_ne_zero ?_ (p_compat i)
        intro h
        have hval : mkRat (q.1 : ℤ) n.1 = (0 : ℚ) := by
          have h' := congrArg Subtype.val h
          simpa using h'
        rw [Rat.mkRat_eq_zero n.2.ne'] at hval
        exact q.2.ne' (by exact_mod_cast hval)⟩) ∈ P


-- For C-TRUE
noncomputable instance : OfNat (ValidIndexedPSpPm I Var Val) 1 where
  ofNat := ⟨1, by aesop⟩

-- For C-TRUE
noncomputable def validOne : ValidIndexedPSpPm I Var Val := 1

-- For C-TRUE
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

-- ## PMF satisfies monadic laws
-- `PMF.instLawfulMonad` comes from `Mathlib.Probability.ProbabilityMassFunction.Constructions`
-- #check PMF.instLawfulMonad

-- ### UNIT-R
theorem Unit_R {A : Type*} {μ : PMF A} :
  PMF.bind μ (λ x ↦ PMF.pure x) = μ := by simp

-- ### UNIT-L
theorem Unit_L {A B : Type*} {v : A} {κ : A → PMF B} :
  PMF.bind (PMF.pure v) κ = κ v := by simp

-- ### ASSOC
theorem Assoc {A B C : Type*} {μ : PMF A} {κ₁ : A → PMF B} {κ₂ : B → PMF C} :
  PMF.bind (PMF.bind μ κ₁) κ₂ = PMF.bind μ (λ x ↦ PMF.bind (κ₁ x) κ₂) := by simp

-- ## 🤖: Helper infrastructure for joint-conditioning rules

open MeasureTheory in
/-- 🤖: A `bind` of a probability measure on the top σ-algebra with a family of probability
measures is again a probability measure (the source space being `⊤`, every function is
measurable). -/
private lemma isProbabilityMeasure_bind_top {A β : Type*} {mβ : MeasurableSpace β}
    (μ : @Measure A ⊤) [IsProbabilityMeasure μ]
    (f : A → @Measure β mβ) (hf : ∀ a, IsProbabilityMeasure (f a)) :
    IsProbabilityMeasure (@Measure.bind A β ⊤ mβ μ f) := by
  constructor
  have hmeas : @Measurable A _ ⊤ _ f := fun s _ => trivial
  rw [Measure.bind_apply MeasurableSet.univ hmeas.aemeasurable]
  simp [measure_univ]

open MeasureTheory in
/-- 🤖: The `PMF`-`bind`/`toMeasure` commutation: the measure of a bound PMF is the measure
bind of the component measures (all on the top σ-algebra). -/
private lemma PMF_toMeasure_bind {A B : Type*} (μ : PMF A) (κ : A → PMF B) :
    @PMF.toMeasure B ⊤ (μ.bind κ)
    = @Measure.bind A B ⊤ ⊤ (@PMF.toMeasure A ⊤ μ) (fun a => @PMF.toMeasure B ⊤ (κ a)) := by
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace B := ⊤
  haveI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  haveI : MeasurableSingletonClass B := ⟨fun _ => trivial⟩
  have hmeas : @Measurable A (Measure B) ⊤ _ (fun a => @PMF.toMeasure B ⊤ (κ a)) :=
    fun s _ => trivial
  ext s hs
  rw [PMF.toMeasure_bind_apply (s := s) μ κ hs, Measure.bind_apply hs hmeas.aemeasurable]
  have hsum : (@PMF.toMeasure A ⊤ μ)
      = Measure.sum (fun a => (μ a : ENNReal) • Measure.dirac a) := by
    ext t ht
    rw [PMF.toMeasure_apply μ ht, Measure.sum_apply _ ht]
    congr 1; ext a
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' a ht, Set.indicator]
    split_ifs <;> simp
  rw [hsum, lintegral_sum_measure]
  congr 1; ext a
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

omit [Finite Var] [Countable Val] in
/-- 🤖: `PSpace.compatiblePerm` depends only on the underlying measurable space and the
permission, not on the measure. Hence any probability measure on `m₀.ms i` is compatible
with `m₀.perm i`, just like `m₀`'s own measure is. -/
private lemma compat_of_ms (m₀ : ValidIndexedPSpPm I Var Val) (i : I)
    (ν : @Measure (Var → Val) (m₀.ms i)) (hν : IsProbabilityMeasure ν) :
    PSpace.compatiblePerm (⟨⟨m₀.ms i, ν⟩, hν⟩ : PSpace (Var → Val)) (m₀.perm i) := by
  obtain ⟨ m₁, h₁ ⟩ := m₀;
  rcases h : m₁ i with ⟨ ⟨ Pm, permm ⟩, hcomp ⟩;
  cases Pm <;> simp_all +decide [ ValidIndexedPSpPm.ms, ValidIndexedPSpPm.perm ];
  · grind;
  · unfold PSp.compatiblePerm at *;
    unfold PSpace.compatiblePerm at *;
    grind +qlia

open MeasureTheory in
/-- 🤖: Compose a `CompatibleKernel B m₀` with a `PMF`-indexed family `κ : A → PMF B`,
giving a `CompatibleKernel A m₀` whose kernel at `(i, a)` is
`bind (κ a) (κ₀.kernel i)`. -/
private def CompatibleKernel.pmfBind {A B : Type*} {m₀ : ValidIndexedPSpPm I Var Val}
    (κ₀ : CompatibleKernel B m₀) (κ : A → PMF B) : CompatibleKernel A m₀ where
  kernel i a := @Measure.bind B (Var → Val) ⊤ (m₀.ms i) (@PMF.toMeasure B ⊤ (κ a)) (κ₀.kernel i)
  isProb i a := by
    letI : MeasurableSpace B := ⊤
    haveI : MeasurableSingletonClass B := ⟨fun _ => trivial⟩
    haveI : IsProbabilityMeasure (@PMF.toMeasure B ⊤ (κ a)) := inferInstance
    exact isProbabilityMeasure_bind_top (@PMF.toMeasure B ⊤ (κ a)) (κ₀.kernel i) (κ₀.isProb i)
  isComp i a := by
    letI : MeasurableSpace B := ⊤
    haveI : MeasurableSingletonClass B := ⟨fun _ => trivial⟩
    haveI : IsProbabilityMeasure (@PMF.toMeasure B ⊤ (κ a)) := inferInstance
    exact compat_of_ms m₀ i _
      (isProbabilityMeasure_bind_top (@PMF.toMeasure B ⊤ (κ a)) (κ₀.kernel i) (κ₀.isProb i))

open MeasureTheory in
omit [Finite Var] [Countable Val] in
/-- 🤖: The outer-bind identity used by `C-UNASSOC`: binding the measure of `μ.bind κ` with a
kernel `κ₀` equals binding the measure of `μ` with the composed kernel `κ₀.pmfBind κ`. -/
private lemma pmfBind_kernel_bind {A B : Type*} {m₀ : ValidIndexedPSpPm I Var Val}
    (κ₀ : CompatibleKernel B m₀) (μ : PMF A) (κ : A → PMF B) (i : I) :
    @Measure.bind B (Var → Val) ⊤ (m₀.ms i) (@PMF.toMeasure B ⊤ (μ.bind κ)) (κ₀.kernel i)
    = @Measure.bind A (Var → Val) ⊤ (m₀.ms i) (@PMF.toMeasure A ⊤ μ)
        ((κ₀.pmfBind κ).kernel i) := by
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSpace B := ⊤
  rw [PMF_toMeasure_bind μ κ]
  exact @Measure.bind_bind A B ⊤ ⊤ (Var → Val) (m₀.ms i) (@PMF.toMeasure A ⊤ μ)
    (fun a => @PMF.toMeasure B ⊤ (κ a)) (κ₀.kernel i)
    measurable_from_top.aemeasurable measurable_from_top.aemeasurable

omit [Finite Var] [Countable Val] in
/-- 🤖: The measure `pp.μ` agrees with the measure of the extracted `PSpace` on every set. -/
private lemma ValidPSpPm.mu_apply_eq_PSpace (pp : ValidPSpPm Var Val)
    (s : Set (Var → Val)) : pp.μ s = (pp.PSpace).1.μ s := by
  obtain ⟨⟨⟨P, perm⟩, hcomp⟩, hv⟩ := pp
  simp only [valid] at hv
  cases P with
  | none => exact absurd rfl hv.1
  | some m' => rfl

omit [Finite Var] [Countable Val] in
/-- 🤖: Indexed version of `ValidPSpPm.mu_apply_eq_PSpace`. -/
private lemma ValidIndexedPSpPm.mu_apply_eq_PSpace (m : ValidIndexedPSpPm I Var Val)
    (i : I) (s : Set (Var → Val)) : m.μ i s = (m.PSpace i).1.μ s :=
  ValidPSpPm.mu_apply_eq_PSpace ⟨m.val i, m.property i⟩ s

omit [Finite Var] [Countable Val] in
/-- 🤖: For a valid indexed space, the underlying `PSp` at index `i` is `some` of the
extracted `PSpace`. -/
private lemma ValidIndexedPSpPm.val_psp_eq_some (m : ValidIndexedPSpPm I Var Val) (i : I) :
    (m.val i).1.1 = some (m.PSpace i) := by
  obtain ⟨mval, mprop⟩ := m
  have hv := mprop i
  simp only [valid] at hv
  rcases hmi : mval i with ⟨⟨Pm, permm⟩, hcomp⟩
  cases hPm : Pm with
  | none =>
    exfalso
    apply hv.1
    have h1 : (↑(mval i) : PSpPmProd Var Val).1 = Pm := by rw [hmi]
    rw [h1, hPm]; rfl
  | some m' => simp only [ValidIndexedPSpPm.PSpace, ValidPSpPm.PSpace, hmi, hPm]; rfl

omit [Finite Var] [Countable Val] in
/-- 🤖: Each component measure `m.μ i` of a valid indexed space is a probability measure. -/
private lemma mu_isProb (m : ValidIndexedPSpPm I Var Val) (i : I) :
    IsProbabilityMeasure (m.μ i) := by
  constructor
  rw [ValidIndexedPSpPm.mu_apply_eq_PSpace m i Set.univ]
  exact (m.PSpace i).2.measure_univ

omit [Finite Var] [Countable Val] in
/-- 🤖: The extracted `PSpace` of a valid indexed space is the measure space built from its
measurable space and measure at that index. -/
private lemma ValidPSpPm.PSpace_eq (pp : ValidPSpPm Var Val) :
    (pp.PSpace).1 = ⟨pp.ms, pp.μ⟩ := by
  obtain ⟨⟨⟨P, perm⟩, hcomp⟩, hv⟩ := pp
  cases P with
  | none => simp only [valid] at hv; exact absurd rfl hv.1
  | some m' => rfl

omit [Finite Var] [Countable Val] in
/-- 🤖: Indexed version of `ValidPSpPm.PSpace_eq`. -/
private lemma PSpace_eq (m : ValidIndexedPSpPm I Var Val) (i : I) :
    (m.PSpace i).1 = ⟨m.ms i, m.μ i⟩ :=
  ValidPSpPm.PSpace_eq ⟨m.val i, m.property i⟩

omit [Finite Var] [Countable Val] in
/-- 🤖: Reconstruction: a valid indexed space equals the indexed space built from its own
measurable spaces, measures, and permissions. Useful to identify the `point space` of a
dirac/self kernel with `m.val`. -/
private lemma val_eq_point (m : ValidIndexedPSpPm I Var Val) :
    (fun i => (⟨⟨some ⟨⟨m.ms i, m.μ i⟩, mu_isProb m i⟩, m.perm i⟩,
      compat_of_ms m i (m.μ i) (mu_isProb m i)⟩ : PSpPm Var Val)) = m.val := by
  funext i
  apply Subtype.ext
  apply Prod.ext
  · show some _ = (m.val i).1.1
    rw [m.val_psp_eq_some i]
    congr 1
    exact Subtype.ext (PSpace_eq m i).symm
  · rfl

/-- 🤖: The constant kernel sending every value to `m`'s own measure at each index. -/
private def CompatibleKernel.constSelf {A : Type*} (m : ValidIndexedPSpPm I Var Val) :
    CompatibleKernel A m where
  kernel i _ := m.μ i
  isProb i _ := mu_isProb m i
  isComp i _ := compat_of_ms m i (m.μ i) (mu_isProb m i)

open MeasureTheory in
/-- 🤖: Binding the dirac PMF's measure with a kernel evaluates the kernel at the point. -/
private lemma dirac_bind_top {A β : Type*} [Countable A] {mβ : MeasurableSpace β}
    (v₀ : A) (k : A → @Measure β mβ) :
    @Measure.bind A β ⊤ mβ (@PMF.toMeasure A ⊤ (δ v₀)) k = k v₀ := by
  letI : MeasurableSpace A := ⊤
  simp only [PMF.dirac]
  rw [Measure.toPMF_toMeasure, Measure.dirac_bind measurable_from_top]

open MeasureTheory in
/-- 🤖: Binding a probability measure with a constant kernel returns that constant. -/
private lemma const_bind_top {A β : Type*} {mβ : MeasurableSpace β}
    (μ : PMF A) (ν : @Measure β mβ) :
    @Measure.bind A β ⊤ mβ (@PMF.toMeasure A ⊤ μ) (fun _ => ν) = ν := by
  letI : MeasurableSpace A := ⊤
  haveI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  rw [Measure.bind_const]
  simp [measure_univ]

-- ## Other helper lemmas

omit [Finite Var] [Countable Val] [DecidableEq Var] [Inhabited Val] in
/-- 🤖: If every `F`-measurable set has measure `0` or `1` under `ps`, then `ps` is the
independent product of its restriction to the sub-σ-algebra `F` and itself.
(Events of measure `0`/`1` are independent of every measurable set.) -/
private lemma psp_trim_indep {ps : PSpace (Var → Val)} {F : MeasurableSpace (Var → Val)}
    (hF : F ≤ ps.1.ms)
    (hbin : ∀ u, @MeasurableSet (Var → Val) F u → ps.1.μ u = 0 ∨ ps.1.μ u = 1) :
    PSpace.isIndependentProduct ps (PSpace.trim (p := ps) (h := hF)) ps := by
  unfold PSpace.isIndependentProduct;
  simp +decide [ PSpace.trim ];
  constructor;
  · refine' le_antisymm _ _;
    · exact fun s hs => MeasurableSpace.measurableSet_generateFrom ( Set.mem_union_right _ hs );
    · exact MeasurableSpace.generateFrom_le fun s hs => by aesop;
  · intro E hE F hF';
    cases hbin E hE <;> simp_all +decide [ MeasureTheory.Measure.trim ];
    · exact MeasureTheory.measure_mono_null ( Set.inter_subset_left ) ‹_›;
    · have h_compl : (ps.1.μ (F \ E)) = 0 := by
        have h_compl : (ps.1.μ (Set.univ \ E)) = 0 := by
          rw [ MeasureTheory.measure_diff ] <;> norm_num [ * ];
          exact MeasurableSet.nullMeasurableSet (hF E hE);
        exact MeasureTheory.measure_mono_null ( fun x => by aesop ) h_compl;
      have h_eq : (ps.1.μ (E ∩ F)) = (ps.1.μ F) - (ps.1.μ (F \ E)) := by
        rw [ ← MeasureTheory.measure_diff ];
        · simp +decide [ Set.inter_comm ];
        · exact Set.diff_subset;
        · exact MeasureTheory.NullMeasurableSet.of_null h_compl;
        · aesop;
      aesop

open MeasureTheory in
omit [Finite Var] [Countable Val] in
/-- 🤖: From `⌈E⟨i⟩⌉` holding on a valid resource `m`, extract a validated
probability space `P` whose space at index `i` is coarser than `m`'s, on which `E` is
a.e.-measurable and the event `{s | E s}` has measure `1`. This packages the forward
content of `Sure_Dirac` in a reusable form. -/
private lemma almostSurely_elim {E : (Var → Val) → Prop} {i : I}
    (m : ValidIndexedPSpPm I Var Val) (h : ⌈E⟨i⟩⌉ m.val) :
    ∃ P : ValidIndexedPSpPm I Var Val,
      P.PSpace i ≤ m.PSpace i ∧
      almostMeasurable E (P.PSp i) ∧
      (P.PSpace i).1.μ {s | E s} = 1 := by
  obtain ⟨q, ⟨P, hqP⟩, hqm⟩ := h
  subst hqP
  obtain ⟨b₁, b₂, hle, hown, body⟩ := hqm
  obtain ⟨p, ⟨a, rfl⟩, hsome⟩ := hown
  obtain ⟨hown_le, hown_some⟩ := hsome
  refine ⟨P, ?_, ?_, ?_⟩
  · have step1 : (⟨⟨P.PSp i, a.perm i⟩, a.comp i⟩ : PSpPm Var Val) ≤ b₁ i := hown_le i
    have step2 : b₁ i ≤ (m.val) i :=
      le_trans (IndexedPSpPm.le_of_mul_left I Val Var i) (hle i)
    have hPm : P.PSp i ≤ (m.val i).1.1 := le_trans step1.1 step2.1
    have hms : (m.val i).1.1 = some (m.PSpace i) := m.val_psp_eq_some i
    have hPs : (P.PSp i) = some (P.PSpace i) := rfl
    rw [hPs, hms] at hPm
    exact WithTop.coe_le_coe.mp hPm
  · simp only [almostMeasurable, ValidIndexedPSpPm.PSp, ValidPSpPm.PSp] at body ⊢
    exact body.1
  · simp only [almostMeasurable, ValidIndexedPSpPm.PSp, ValidPSpPm.PSp] at body
    obtain ⟨ham, hμ⟩ := body
    have bridge : @Measure.map _ _ (P.ms i) ⊤ E (P.μ i)
        = @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ :=
      ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ E
    rw [bridge] at hμ
    have hae : AEMeasurable E (P.PSpace i).1.μ := by
      simpa [ValidIndexedPSpPm.PSpace] using ham
    have key := Measure.map_apply_of_aemeasurable (mβ := ⊤) hae
      (s := {True}) MeasurableSpace.measurableSet_top
    rw [hμ] at key
    simp only [PMF.dirac, Measure.toPMF_toMeasure,
      Measure.dirac_apply', MeasurableSpace.measurableSet_top] at key
    simp only [Set.indicator_of_mem, Set.mem_singleton_iff, Pi.one_apply] at key
    rw [key]
    congr 1
    ext s
    simp [Set.mem_setOf_eq]

open MeasureTheory in
omit [Finite Var] [Countable Val] in
/-- 🤖: If `⌈E⟨i⟩⌉` holds on a valid resource `m`, then `E` holds
`m.PSpace i`-almost everywhere. -/
private lemma almostSurely_ae {E : (Var → Val) → Prop} {i : I}
    (m : ValidIndexedPSpPm I Var Val) (h : ⌈E⟨i⟩⌉ m.val) :
    ∀ᵐ s ∂(m.PSpace i).1.μ, E s := by
  obtain ⟨ P, hPle, ham, hP1 ⟩ := almostSurely_elim m h;
  -- Let `μP := (P.PSpace i).1.μ`.
  set μP := (P.PSpace i).1.μ;
  -- Show `f ⁻¹' {True}` has measure 1 and hence `f ⁻¹' {False}` has measure 0.
  obtain ⟨ f, hf_meas, hf_ae ⟩ := ham;
  have h_true : μP (f ⁻¹' {True}) = 1 := by
    rw [ ← hP1, ← MeasureTheory.measure_congr ];
    filter_upwards [ hf_ae ] with s hs using by simpa using hs;
  have h_false : μP (f ⁻¹' {False}) = 0 := by
    convert MeasureTheory.measure_compl _ _ using 1;
    convert rfl;
    any_goals exact f ⁻¹' { True };
    · ext; simp [Set.mem_compl_iff];
    · rw [ h_true, ( P.PSpace i ).2.measure_univ, tsub_self ];
    · exact hf_meas ( MeasurableSingletonClass.measurableSet_singleton _ );
    · exact h_true.symm ▸ ENNReal.one_ne_top;
  obtain ⟨ N2, hN2_sub, hN2_meas, hN2_null ⟩ := @exists_measurable_superset_of_null _ ( P.PSpace i ).1.ms μP _ hf_ae.symm;
  refine' MeasureTheory.measure_mono_null _ _;
  exact N2 ∪ f ⁻¹' { False };
  · grind +qlia;
  · exact MeasureOnSpace.le_preserves_measure hPle ( hN2_meas.union ( hf_meas ( MeasurableSingletonClass.measurableSet_singleton _ ) ) ) |> fun h => h.symm ▸ MeasureTheory.measure_union_null hN2_null h_false

omit [Finite Var] [Countable Val] in
/-- 🤖: A valid indexed space owns its own underlying spaces. -/
private lemma ownPSp_self (m : ValidIndexedPSpPm I Var Val) :
    ownPSp m.PSp m.val := by
  constructor;
  refine' ⟨ ⟨ _, rfl ⟩, _ ⟩;
  constructor;
  exact fun i => m.val_psp_eq_some i ▸ ( m.val i ).2;
  constructor;
  · intro i;
    constructor;
    · exact m.val_psp_eq_some i ▸ le_rfl;
    · exact le_rfl;
  · exact fun i => by cases m.val i ; tauto;

omit [Finite Var] [Countable Val] in
/-- 🤖: Converse of `almostSurely_ae`: if `E` holds `m.PSpace i`-almost everywhere, then
`⌈E⟨⟨i⟩⌉` holds on `m`. The witness space is `m` itself. -/
private lemma almostSurely_intro {E : (Var → Val) → Prop} {i : I}
    (m : ValidIndexedPSpPm I Var Val) (h : ∀ᵐ s ∂(m.PSpace i).1.μ, E s) :
    ⌈E⟨i⟩⌉ m.val := by
  refine' ⟨ _, ⟨ m, rfl ⟩, _ ⟩;
  refine' ⟨ m.val, 1, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  · exact mul_one _ |> le_of_eq;
  · exact ownPSp_self m;
  · refine' ⟨ _, _ ⟩;
    · refine' ⟨ fun _ => True, measurable_const, h.mono fun s hs => by simpa using hs ⟩;
    · have hE_true : E =ᵐ[(m.PSpace i).1.μ] (fun _ => True) := by
        filter_upwards [ h ] with s hs using by simpa using hs;
      convert Measure.map_congr hE_true using 1;
      · convert ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨ m.val i, m.property i ⟩ E using 1;
      · ext s hs; simp +decide only [PMF.dirac, Measure.toPMF_toMeasure,
        MeasurableSpace.measurableSet_top, Measure.dirac_apply', ValidIndexedPSpPm.PSpace,
        PSp.compatiblePerm, OrderedUnitalResourceAlgebra.instValidForall.eq_1, ValidPSpPm.PSpace,
        ValidPSpPm, ValidPSp.PSpace, ValidPSp, Measure.map_const, PSpace.isProbability,
        measure_univ, one_smul] ;

omit [Finite Var] [Countable Val] in 
/-- 🤖: Forward direction of SURE-MERGE. Mirrors the proof of `Sure_Eq_Inj`: from
`b₁ * b₂ ≤ m` both sure assertions transfer to a.e. statements under the *same*
measure `(⟨m,hm⟩.PSpace i).1.μ` (via `almostSurely_ae` together with
`IndexedPSpPm.le_of_mul_left`/`le_of_mul_right`), their conjunction holds a.e.,
and `almostSurely_intro` concludes the merged sure assertion. -/
private lemma Sure_Merge_fwd {E₁ E₂ : (Var → Val) → Prop} {i : I}
  : ⌈E₁⟨i⟩⌉ ∗ ⌈E₂⟨i⟩⌉ ⊢ ⌈(fun s => E₁ s ∧ E₂ s)⟨i⟩⌉ := by
  intro m hm hsep
  obtain ⟨b₁, b₂, hle, h1, h2⟩ := hsep
  set M : ValidIndexedPSpPm I Var Val := ⟨m, hm⟩ with hM
  have a1 : ∀ᵐ s ∂(M.PSpace i).1.μ, E₁ s := by
    apply almostSurely_ae M
    exact (almostSurely E₁ i).upper'
      (le_trans (IndexedPSpPm.le_of_mul_left I Val Var) hle) h1
  have a2 : ∀ᵐ s ∂(M.PSpace i).1.μ, E₂ s := by
    apply almostSurely_ae M
    exact (almostSurely E₂ i).upper'
      (le_trans (IndexedPSpPm.le_of_mul_right I Val Var) hle) h2
  have a3 : ∀ᵐ s ∂(M.PSpace i).1.μ, E₁ s ∧ E₂ s := by
    filter_upwards [a1, a2] with s hs1 hs2 using ⟨hs1, hs2⟩
  exact almostSurely_intro M a3

open MeasureTheory in
private lemma pmf_tsum_subtype_eq_one_iff {A : Type*} {X : Set A} {μ : PMF A} :
    (∑' x : X, μ x = 1) ↔ (∀ v, v ∈ μ.support → v ∈ X) := by
  letI : MeasurableSpace A := ⊤
  haveI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  have hX : ∑' x : X, (μ x) = μ.toMeasure X := by
    rw [tsum_subtype]; exact (PMF.toMeasure_apply μ (by trivial : MeasurableSet X)).symm
  have hcompl : μ.toMeasure Xᶜ = 1 - μ.toMeasure X := by
    rw [measure_compl (by trivial) (measure_ne_top _ _)]; simp
  rw [hX]
  rw [show (μ.toMeasure X = 1) ↔ (μ.toMeasure Xᶜ = 0) from by
    rw [hcompl]
    constructor
    · intro h; rw [h, tsub_self]
    · intro h
      have hle : μ.toMeasure X ≤ 1 := prob_le_one
      rw [tsub_eq_zero_iff_le] at h
      exact le_antisymm hle h]
  rw [PMF.toMeasure_apply_eq_zero_iff μ (by trivial : MeasurableSet Xᶜ)]
  constructor
  · intro hdis v hv
    by_contra hvX
    exact (Set.disjoint_left.mp hdis hv) hvX
  · intro h
    rw [Set.disjoint_left]
    intro v hv hvc
    exact hvc (h v hv)


/-- 🤖: The function `b ↦ ∑' a ∈ f⁻¹'{b}, μ a` is a `PMF`, i.e. it sums to `1`.
This is precisely the pushforward distribution `μ.map f`. -/
private lemma pmf_pushforward_hasSum {A B : Type*} (μ : PMF A) (f : A → B) :
    HasSum (fun b => ∑' a : f ⁻¹' {b}, μ a) 1 := by
  classical
  have heq : (fun b => ∑' a : f ⁻¹' {b}, μ a) = (μ.map f) := by
    ext b
    rw [PMF.map_apply, tsum_subtype]
    congr 1; ext a
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    by_cases h : f a = b
    · simp [h]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [heq]
  exact (μ.map f).2

private lemma pushforward_eq_map {A B : Type*} (μ : PMF A) (f : A → B) :
    (⟨fun b ↦ ∑' a : f ⁻¹' {b}, μ a, pmf_pushforward_hasSum μ f⟩ : PMF B) = μ.map f := by
  classical
  apply PMF.ext
  intro b
  show ∑' a : f ⁻¹' {b}, μ a = _
  rw [PMF.map_apply, tsum_subtype]
  congr 1; ext a
  simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
  by_cases hh : f a = b
  · simp [hh]
  · rw [if_neg hh, if_neg (fun hx => hh hx.symm)]

omit [Finite Var] [Countable Val] in
/-- 🤖: Indexed version of `ValidPSpPm.map_μ_eq_map_PSpace_μ`: pushing `E` forward along the
indexed measure `m.μ i` agrees with pushing it along the extracted `PSpace` measure. -/
private lemma ValidIndexedPSpPm.map_μ_eq_map_PSpace_μ {A : Type*}
    (m : ValidIndexedPSpPm I Var Val) (i : I) (E : (Var → Val) → A) :
    @Measure.map _ _ (m.ms i) ⊤ E (m.μ i)
    = @Measure.map _ _ (m.PSpace i).1.ms ⊤ E (m.PSpace i).1.μ :=
  ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨m.val i, m.property i⟩ E

open MeasureTheory in
omit [Finite Var] [Countable Val] [DecidableEq Var] [Inhabited Val] in
/-- 🤖: The `bind` of a `PMF`'s measure with a measure kernel equals the countable
`Measure.sum`, over the (countable) support of `μ`, of the scaled kernels `(μ a) • κ a`.
The terms off the support vanish since `μ a = 0` there. -/
private lemma pmf_bind_eq_sum_support {A : Type*}
    {ms : MeasurableSpace (Var → Val)}
    (μ : PMF A) (κ : A → @Measure (Var → Val) ms) :
    @Measure.bind A (Var → Val) ⊤ ms (@PMF.toMeasure A ⊤ μ) κ
    = @Measure.sum (Var → Val) μ.support ms (fun a => (μ ↑a) • κ ↑a) := by
  ext s hs
  simp [Measure.bind, Measure.sum] at *;
  unfold Measure.join; simp +decide [ hs, measurable_from_top ] ;
  rw [ Measure.ofMeasurable_apply ] ; simp +decide [ PMF.map ] ; (
  -- 🤖: Apply the definition of the integral with respect to a discrete measure.
  have h_integral : ∫⁻ (μ : Measure (Var → Val)), μ s ∂(μ.bind (PMF.pure ∘ κ)).toMeasure = ∑' (a : A), μ a * (κ a) s := by
    have h_discrete : (μ.bind (PMF.pure ∘ κ)).toMeasure = Measure.sum (fun a => (μ a) • Measure.dirac (κ a)) := by
      ext s hs; simp +decide [ hs ] ;
      simp +decide [ Set.indicator ]
    rw [ h_discrete, MeasureTheory.lintegral_sum_measure ] ; simp +decide [ MeasureTheory.lintegral_smul_measure ] ;
    congr! 2;
    rw [ MeasureTheory.lintegral_dirac' ];
    exact Measure.measurable_coe hs;
  convert h_integral using 1;
  rw [ tsum_eq_tsum_of_ne_zero_bij ];
  use fun x => ⟨ x, by
    exact fun h => x.2 <| by simp +decide [ h ] ; ⟩
  all_goals generalize_proofs at *;
  · exact fun x y h => Subtype.ext <| by simpa using congr_arg Subtype.val h;
  · exact fun x hx => ⟨ ⟨ x, by aesop ⟩, rfl ⟩;
  · grobner);
  grind

open MeasureTheory in
omit [Finite Var] [Countable Val] [DecidableEq Var] [Inhabited Val] in
/-- 🤖: `E` is a.e.-measurable under the `bind` of a `PMF` with a measure kernel whenever it is
a.e.-measurable under every kernel in the support. The `bind` is a countable `Measure.sum`
of scaled kernels, and a.e.-measurability is preserved by countable sums of measures. -/
private lemma aemeasurable_pmf_bind {A B : Type*} {mB : MeasurableSpace B}
    {ms : MeasurableSpace (Var → Val)}
    (μ : PMF A) (κ : A → @Measure (Var → Val) ms) (E : (Var → Val) → B)
    (h : ∀ a : μ.support, @AEMeasurable _ _ mB ms E (κ a)) :
    @AEMeasurable _ _ mB ms E
      (@Measure.bind A (Var → Val) ⊤ ms (@PMF.toMeasure A ⊤ μ) κ) := by
  haveI : Countable μ.support := μ.support_countable.to_subtype
  rw [pmf_bind_eq_sum_support μ κ]
  exact AEMeasurable.sum_measure (fun a => (h a).smul_measure _)

open MeasureTheory in
omit [Finite Var] [Countable Val] [DecidableEq Var] [Inhabited Val] in
/-- 🤖: If, for every point in the support of `μ`, pushing `E` forward along the kernel `κ`
gives the same measure `ν`, then pushing `E` forward along the `bind` also gives `ν`
(the total mass of `μ` being `1`). -/
private lemma map_pmf_bind_const {A B : Type*} {mB : MeasurableSpace B}
    {ms : MeasurableSpace (Var → Val)}
    (μ : PMF A) (κ : A → @Measure (Var → Val) ms) (E : (Var → Val) → B) (ν : @Measure B mB)
    (hae : ∀ a : μ.support, @AEMeasurable _ _ mB ms E (κ a))
    (hmap : ∀ a : μ.support, @Measure.map _ _ ms mB E (κ a) = ν) :
    @Measure.map _ _ ms mB E
      (@Measure.bind A (Var → Val) ⊤ ms (@PMF.toMeasure A ⊤ μ) κ) = ν := by
  convert Measure.ext _;
  intro s hs; rw [pmf_bind_eq_sum_support μ κ]; simp_all +decide [ Measure.map_sum, Measure.smul_apply ] ;
  convert congr_arg ( fun x : ENNReal => x * ν s ) ( show ∑' ( i : μ.support ), μ ↑i = 1 from ?_ ) using 1;
  · rw [ ← ENNReal.tsum_mul_right ] ; congr ; ext a ; aesop;
  · rw [ one_mul ];
  · exact pmf_tsum_subtype_eq_one_iff.mpr fun v a => a

open MeasureTheory in
omit [Finite Var] [Countable Val] [DecidableEq Var] [Inhabited Val] in
/-- 🤖: Measure-level core: if `μq` extends `μp` along `msp ≤ msq` (they agree on `msp`-measurable
sets) and `E` is `μp`-a.e.-measurable, then `E` is `μq`-a.e.-measurable and
`map E μq = map E μp`. -/
private lemma map_eq_map_of_measure_le {A : Type*}
    {msp msq : MeasurableSpace (Var → Val)}
    (μp : @Measure (Var → Val) msp) (μq : @Measure (Var → Val) msq)
    (hms : msp ≤ msq)
    (hrestrict : ∀ u, MeasurableSet[msp] u → μp u = μq u)
    {E : (Var → Val) → A}
    (hae : @AEMeasurable _ _ ⊤ msp E μp) :
    @AEMeasurable _ _ ⊤ msq E μq ∧
    @Measure.map _ _ msq ⊤ E μq = @Measure.map _ _ msp ⊤ E μp := by
  obtain ⟨g, hg₁, hg₂⟩ := hae
  have hnull : μp {x | E x ≠ g x} = 0 :=
    MeasureTheory.measure_mono_null (fun x hx => by aesop) hg₂
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ :=
    @MeasureTheory.exists_measurable_superset_of_null (Var → Val) msp μp {x | E x ≠ g x} hnull
  have hNzero_q : μq N = 0 := by rw [← hrestrict N hNmeas]; exact hNzero
  have hg₂q : E =ᵐ[μq] g :=
    MeasureTheory.measure_mono_null (fun x hx => hNsub hx) hNzero_q
  have haeq : @AEMeasurable _ _ ⊤ msq E μq := ⟨g, hg₁.mono hms le_rfl, hg₂q⟩
  refine ⟨haeq, ?_⟩
  refine @MeasureTheory.Measure.ext A ⊤ _ _ (fun s hs => ?_)
  rw [Measure.map_apply_of_aemeasurable haeq hs,
      Measure.map_apply_of_aemeasurable (⟨g, hg₁, hg₂⟩ : @AEMeasurable _ _ ⊤ msp E μp) hs]
  have hcongr_q : μq (E ⁻¹' s) = μq (g ⁻¹' s) :=
    MeasureTheory.measure_congr (hg₂q.fun_comp (· ∈ s))
  have hcongr_p : μp (E ⁻¹' s) = μp (g ⁻¹' s) :=
    MeasureTheory.measure_congr (hg₂.fun_comp (· ∈ s))
  rw [hcongr_q, hcongr_p]
  exact (hrestrict (g ⁻¹' s) (hg₁ hs)).symm

open MeasureTheory in
omit [Finite Var] [Countable Val] [DecidableEq Var] [Inhabited Val] in
/-- 🤖: If `p ≤ q` as probability spaces (so `q` extends `p`'s σ-algebra and restricts to `p`'s
measure) and `E` is `p`-a.e.-measurable, then `E` is also `q`-a.e.-measurable and its
pushforward is unchanged: `map E q.μ = map E p.μ`. -/
private lemma map_eq_map_of_pspace_le {A : Type*} {p q : PSpace (Var → Val)}
    (hpq : p ≤ q) {E : (Var → Val) → A}
    (hae : @AEMeasurable _ _ ⊤ p.1.ms E p.1.μ) :
    @AEMeasurable _ _ ⊤ q.1.ms E q.1.μ ∧
    @Measure.map _ _ q.1.ms ⊤ E q.1.μ = @Measure.map _ _ p.1.ms ⊤ E p.1.μ :=
  map_eq_map_of_measure_le p.1.μ q.1.μ hpq.1
    (fun _ hu => MeasureOnSpace.le_preserves_measure hpq hu) hae

open MeasureTheory in
omit [Finite Var] [Countable Val] in
/-- 🤖: Witness-extraction form of distribution ownership: `E⟨i⟩ ~ ν` on `m` yields a coarser
validated space `P` (with `P.PSpace i ≤ m.PSpace i`) on which `E` is a.e.-measurable and
pushes forward to `ν`. This repackages the destructuring at the start of `almostSurely_elim`
for an arbitrary `ν`. -/
private lemma hasDistribution_witness {A : Type*} {E : (Var → Val) → A} {i : I} {ν : PMF A}
    (m : ValidIndexedPSpPm I Var Val) (h : (E⟨i⟩ ~ ν) m.val) :
    ∃ P : ValidIndexedPSpPm I Var Val, P.PSpace i ≤ m.PSpace i ∧
      @AEMeasurable _ _ ⊤ (P.PSpace i).1.ms E (P.PSpace i).1.μ ∧
      @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ = @PMF.toMeasure A ⊤ ν := by
  obtain ⟨q, ⟨P, rfl⟩, hqm⟩ := h
  obtain ⟨b₁, b₂, hle, hown, body⟩ := hqm
  obtain ⟨p, ⟨a, rfl⟩, hsome⟩ := hown
  obtain ⟨hown_le, hown_some⟩ := hsome
  refine ⟨P, ?_, ?_, ?_⟩
  · have step1 : (⟨⟨P.PSp i, a.perm i⟩, a.comp i⟩ : PSpPm Var Val) ≤ b₁ i := hown_le i
    have step2 : b₁ i ≤ (m.val) i :=
      le_trans (IndexedPSpPm.le_of_mul_left I Val Var i) (hle i)
    have hPm : P.PSp i ≤ (m.val i).1.1 := le_trans step1.1 step2.1
    have hms : (m.val i).1.1 = some (m.PSpace i) := m.val_psp_eq_some i
    have hPs : (P.PSp i) = some (P.PSpace i) := rfl
    rw [hPs, hms] at hPm
    exact WithTop.coe_le_coe.mp hPm
  · simp only [almostMeasurable, ValidIndexedPSpPm.PSp, ValidPSpPm.PSp] at body ⊢
    exact body.1
  · obtain ⟨ham, hμ⟩ := body
    have bridge : @Measure.map _ _ (P.ms i) ⊤ E (P.μ i)
        = @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ :=
      ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ E
    rw [bridge] at hμ
    exact hμ

open MeasureTheory in
omit [Finite Var] [Countable Val] in
/-- 🤖: Elimination form of distribution ownership: if `E⟨i⟩ ~ ν` holds on a valid resource `m`,
then `E` is a.e.-measurable under `m.μ i` and pushing `E` forward along `m.μ i` yields `ν`.
Generalizes the sure-assertion `almostSurely_elim`/`almostSurely_ae` to an arbitrary `ν`.
The witness space `P` for the distribution assertion is coarser than `m`, but `E`'s
pushforward transfers to `m` because `P.PSpace i ≤ m.PSpace i` and `E` is `P`-a.e.-measurable. -/
private lemma hasDistribution_elim {A : Type*} {E : (Var → Val) → A} {i : I} {ν : PMF A}
    (m : ValidIndexedPSpPm I Var Val) (h : (E⟨i⟩ ~ ν) m.val) :
    @AEMeasurable _ _ ⊤ (m.PSpace i).1.ms E (m.PSpace i).1.μ
    ∧ @Measure.map _ _ (m.ms i) ⊤ E (m.μ i) = @PMF.toMeasure A ⊤ ν := by
  obtain ⟨P, hPle, hae, hmap⟩ := hasDistribution_witness m h
  obtain ⟨hae_m, hmap_m⟩ := map_eq_map_of_pspace_le hPle hae
  have hbridge_m : @Measure.map _ _ (m.ms i) ⊤ E (m.μ i)
      = @Measure.map _ _ (m.PSpace i).1.ms ⊤ E (m.PSpace i).1.μ :=
    ValidIndexedPSpPm.map_μ_eq_map_PSpace_μ m i E
  exact ⟨hae_m, by rw [hbridge_m, hmap_m, hmap]⟩

omit [Finite Var] [Countable Val] in
/-- 🤖: The `PSpace`-form and `m.μ i`-form of a.e.-measurability of `E` at index `i` coincide
(the extracted `PSpace` measure/σ-algebra are definitionally `m`'s at a valid index). -/
private lemma ValidPSpPm.aemeasurable_PSpace_iff_μ {A : Type*} (pp : ValidPSpPm Var Val)
    {E : (Var → Val) → A} :
    @AEMeasurable _ _ ⊤ pp.PSpace.1.ms E pp.PSpace.1.μ ↔ @AEMeasurable _ _ ⊤ pp.ms E pp.μ := by
  obtain ⟨⟨⟨P, perm⟩, hcomp⟩, hv⟩ := pp
  simp only [valid] at hv
  cases P with
  | none => exact absurd rfl hv.1
  | some m' => exact Iff.rfl

omit [Finite Var] [Countable Val] in
private lemma ValidIndexedPSpPm.aemeasurable_PSpace_iff_μ {A : Type*}
    (m : ValidIndexedPSpPm I Var Val) (i : I) {E : (Var → Val) → A} :
    @AEMeasurable _ _ ⊤ (m.PSpace i).1.ms E (m.PSpace i).1.μ
      ↔ @AEMeasurable _ _ ⊤ (m.ms i) E (m.μ i) :=
  ValidPSpPm.aemeasurable_PSpace_iff_μ ⟨m.val i, m.property i⟩

omit [Finite Var] [Countable Val] in
/-- 🤖: The extracted `PSpace` measure and `m.μ i` induce the same almost-everywhere filter. -/
private lemma ValidPSpPm.ae_PSpace_iff_μ (pp : ValidPSpPm Var Val)
    {P : (Var → Val) → Prop} :
    (∀ᵐ s ∂pp.PSpace.1.μ, P s) ↔ (∀ᵐ s ∂pp.μ, P s) := by
  obtain ⟨⟨⟨Q, perm⟩, hcomp⟩, hv⟩ := pp
  simp only [valid] at hv
  cases Q with
  | none => exact absurd rfl hv.1
  | some m' => exact Iff.rfl

omit [Finite Var] [Countable Val] in
private lemma ValidIndexedPSpPm.ae_PSpace_iff_μ (m : ValidIndexedPSpPm I Var Val) (i : I)
    {P : (Var → Val) → Prop} :
    (∀ᵐ s ∂(m.PSpace i).1.μ, P s) ↔ (∀ᵐ s ∂(m.μ i), P s) :=
  ValidPSpPm.ae_PSpace_iff_μ ⟨m.val i, m.property i⟩

omit [Finite Var] [Countable Val] in
/-- 🤖: Introduction form of distribution ownership: if `E` is a.e.-measurable under `m.μ i` and
pushes forward to `μ`, then `E⟨i⟩ ~ μ` holds on `m.val` (witnessed by `m` itself). Dual to
`hasDistribution_elim`; generalizes `almostSurely_intro`. -/
private lemma hasDistribution_intro {A : Type*} {E : (Var → Val) → A} {i : I} {μ : PMF A}
    (m : ValidIndexedPSpPm I Var Val)
    (hae : @AEMeasurable _ _ ⊤ (m.ms i) E (m.μ i))
    (hmap : @Measure.map _ _ (m.ms i) ⊤ E (m.μ i) = @PMF.toMeasure A ⊤ μ) :
    (E⟨i⟩ ~ μ) m.val := by
  refine ⟨_, ⟨m, rfl⟩, m.val, 1, (mul_one _).le, ownPSp_self m, ?_, ?_⟩
  · show almostMeasurable E (m.PSp i)
    rw [show m.PSp i = some (m.PSpace i) from rfl]
    exact (ValidIndexedPSpPm.aemeasurable_PSpace_iff_μ m i).2 hae
  · exact hmap

-- # The primitive (non-WP) rules of Bluebell (see Fig. 9)

-- ## Distribution ownership rules

-- ### AND-TO-STAR

-- #### AND-TO-STAR: Helper lemmas

open Classical in
omit [Finite Var] [Countable Val] in
/-- Auxiliary: for a valid element `a` and a valid witness `a'` agreeing with `a` on
`J₁ ∩ J₂` (where both `J₁, J₂` are in the idx-family), `P a` holds.
The key idea is to construct a valid intermediate element that agrees with `a'` on `J₂`
and with `a` on `J₁`, using the validity of both `a` and `a'`. -/
private lemma irrelevant_binary_inter
  {P : bProp I Var Val} {J₁ J₂ : Set I}
  (hJ₁ : irrelevant {i | i ∉ J₁} P) (hJ₂ : irrelevant {i | i ∉ J₂} P)
  {a a' : IndexedPSpPm I Var Val}
  (hva : valid a) (hva' : valid a')
  (hagree : ∀ i, i ∈ J₁ ∩ J₂ → a i = a' i) (hPa' : P a') : P a := by
  -- Define intermediate: a on J₁, a' on J₁ᶜ
  set a₁ : IndexedPSpPm I Var Val := fun i => if i ∈ J₁ then a i else a' i
  -- a₁ is valid
  have hva₁ : valid a₁ := by
    intro i; dsimp [a₁]
    split <;> [exact hva i; exact hva' i]
  -- a₁ agrees with a' on J₂
  have h₂ : ∀ i, i ∈ J₂ → a₁ i = a' i := by
    intro i hi₂; dsimp [a₁]
    split
    · rename_i hi₁; exact hagree i ⟨hi₁, hi₂⟩
    · rfl
  -- P a₁ by irrelevant J₂ᶜ
  have hPa₁ : P a₁ := by
    apply hJ₂; exact ⟨a', hva', fun i hi => h₂ i (by rwa [Set.mem_setOf_eq, not_not] at hi), hPa'⟩
  -- a agrees with a₁ on J₁
  have h₁ : ∀ i, i ∈ J₁ → a i = a₁ i := by
    intro i hi; dsimp [a₁]; rw [if_pos hi]
  -- P a by irrelevant J₁ᶜ
  exact hJ₁ a ⟨a₁, hva₁, fun i hi => h₁ i (by rwa [Set.mem_setOf_eq, not_not] at hi), hPa₁⟩

open Classical in
omit [Finite Var] [Countable Val] in
/-- For a finite family of sets satisfying irrelevance, the intersection also satisfies
irrelevance when both elements are valid. Proved by finite induction on the family. -/
private lemma irrelevant_sInter_valid [Inhabited Var] [Finite I]
  {P : bProp I Var Val} {S : Set (Set I)} (hS : ∀ J ∈ S, irrelevant {i | i ∉ J} P)
  {a a' : IndexedPSpPm I Var Val} (hva : valid a) (hva' : valid a')
  (hagree : ∀ i, i ∈ ⋂₀ S → a i = a' i) (hPa' : P a') : P a := by
  contrapose! hPa';
  have h_finite_S : Set.Finite S := by
    exact Set.toFinite S;
  have h_ind : ∀ (S : Finset (Set I)), (∀ J ∈ S, irrelevant {i | i ∉ J} P) → ∀ (a a' : IndexedPSpPm I Var Val), valid a → valid a' → (∀ i ∈ ⋂₀ S, a i = a' i) → P a' → P a := by
    intro S hS a a' hva hva' hagree hPa'
    induction' S using Finset.induction with J S hS ih generalizing a a';
    · convert hPa' using 1;
      exact funext fun i => hagree i ( by simp +decide ) ▸ rfl;
    · -- Define intermediate c : IndexedPSpPm I Var Val as c i = a i if i ∈ J, a' i if i ∉ J.
      set c : IndexedPSpPm I Var Val := fun i => if i ∈ J then a i else a' i;
      have hc_valid : valid c := by
        exact fun i => by unfold c; split_ifs <;> [ exact hva i; exact hva' i ] ;
      have hc_agree : ∀ i ∈ ⋂₀ S, c i = a' i := by
        grind +splitImp;
      have hc_P : P c := by
        exact ih ( fun J hJ => hS J ( Finset.mem_insert_of_mem hJ ) ) c a' hc_valid hva' hc_agree hPa';
      have := hS J ( Finset.mem_insert_self _ _ );
      apply this;
      grind +revert;
  exact fun h => hPa' <| h_ind h_finite_S.toFinset ( fun J hJ => hS J <| h_finite_S.mem_toFinset.mp hJ ) a a' hva hva' ( fun i hi => hagree i <| by simpa using hi ) h

open Classical in
omit [Finite Var] [Countable Val] in
/-- The key locality property: `P` is irrelevant to indices outside `idx P`.
This is stated in the Bluebell paper (p.17) as a property of the `idx` definition.
When `I` is finite, the family `{J | irrelevant {i | i ∉ J} P}` is finite, so the
arbitrary intersection `idx P` inherits the irrelevance property via
`irrelevant_sInter_valid` and the `UpperSet` structure of assertions. -/
private lemma irrelevant_idx_compl [Inhabited Var] [Finite I]
  (P : bProp I Var Val) : irrelevant {i | i ∉ idx P} P := by
  intro a ha;
  obtain ⟨a', ha', hagree', hPa'⟩ := ha
  set a₀ : IndexedPSpPm I Var Val := fun i => if i ∈ idx P then a' i else 1;
  -- By definition of $a₀$, we know that $a₀$ is valid.
  have ha₀_valid : valid a₀ := by
    aesop;
  -- By definition of $a₀$, we know that $a₀$ and $a'$ agree on $\text{idx } P$.
  have ha₀_a'_agree : ∀ i ∈ idx P, a₀ i = a' i := by
    aesop;
  -- By definition of $a₀$, we know that $P a₀$.
  have ha₀_P : P a₀ := by
    apply_rules [ irrelevant_sInter_valid ];
    exact fun J hJ => hJ;
  convert P.upper' _ ha₀_P using 1;
  intro i; by_cases hi : i ∈ idx P <;> simp_all +decide ;
  convert IndexedPSpPm.one_le ( I := I ) ( Var := Var ) ( Val := Val ) ( a := a ) i using 1;
  aesop

-- #### AND-TO-STAR: Spec & Proof

open Classical in
omit [Finite Var] [Countable Val] in
theorem And_To_Star [Inhabited Var] [Finite I]
  (P Q : bProp I Var Val) :
      idx P ∩ idx Q = ∅
    → P ∧ Q ⊢ P ∗ Q := by
  intro hdisj m hv ⟨hPm, hQm⟩
  -- Construct b₁ = m on idx P, 1 elsewhere; b₂ = m on (idx P)ᶜ, 1 on idx P
  refine ⟨fun i => if i ∈ idx P then m i else 1,
          fun i => if i ∈ idx P then 1 else m i, ?_, ?_, ?_⟩
  · -- b₁ * b₂ ≤ m
    intro i
    simp only [Pi.mul_apply]
    by_cases hi : i ∈ idx P
    · simp [hi]
    · simp [hi]
  · -- P b₁
    exact irrelevant_idx_compl P (fun i => if i ∈ idx P then m i else 1)
      ⟨m, hv, fun i hi => by simp only [Set.mem_setOf_eq, not_not] at hi; simp [hi], hPm⟩
  · -- Q b₂
    have hcompl : irrelevant {i | i ∉ idx Q} Q := irrelevant_idx_compl Q
    apply hcompl
    refine ⟨m, hv, fun i hi => ?_, hQm⟩
    simp only [Set.mem_setOf_eq, not_not] at hi
    have hni : i ∉ idx P := by
      intro hip
      have : i ∈ idx P ∩ idx Q := ⟨hip, hi⟩
      rw [hdisj] at this
      exact this.elim
    simp [hni]

-- ### DIST-INJ

open MeasureTheory in
omit [Finite Var] [Countable Val] in
theorem Dist_Inj
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

-- ### SURE-MERGE

theorem Sure_Merge
  {A : Type*}
  {E₁ E₂ : (Var → Val) → Prop} {i : I}
  : ⌈E₁⟨i⟩⌉ ∗ ⌈E₂⟨i⟩⌉ ⊣⊢ ⌈(fun s => E₁ s ∧ E₂ s)⟨i⟩⌉ := by
    constructor
    · exact Sure_Merge_fwd
    · sorry

-- ### SURE-AND-STAR

theorem Sure_And_Star [DecidableEq I] {i : I} {A : Type*}
  {P : bProp I Var Val}
  {E : (Var → Val) → Prop} :
  pabs P (fun e ↦ e.1 = i ∧ e.2 ∈ pvar E) →
  ⌈E⟨i⟩⌉ ∧ P ⊢ ⌈E⟨i⟩⌉ ∗ P := by
    sorry -- TODO: Rule SURE-AND-STAR proof

-- ### PROD-SPLIT

theorem Prod_Split {i : I} {A B : Type*}
  {μ₁ : PMF A} {μ₂ : PMF B}
  {E₁ : (Var → Val) → A} {E₂ : (Var → Val) → B} :
  (fun s => (E₁ s, E₂ s))⟨i⟩ ~ (μ₁ ⊗ μ₂)
  ⊢ E₁⟨i⟩ ~ μ₁ ∗ E₂⟨i⟩ ~ μ₂ := by
    sorry -- TODO: Rule PROD-SPLIT proof

-- ## Joint conditioning rules

-- ### C-TRUE

theorem C_True
  {A : Type*} {μ : PMF A}
  : ⊢ (𝒞⟨μ⟩ _v; BTrue : bProp I Var Val) := by
  unfold jointConditioning
  iexists 1, k
  isplitl
  · intro m _ _ i
    have := @IndexedPSpPm.one_le I Val Var _ _ m i
    trivial
  · isplitl
    · apply Iris.BI.forall_intro
      intro i _ _ _
      have : (@ValidIndexedPSpPm.μ I Var Val _ _) 1 i
        = (1 : MeasureOnSpace (Var → Val)).μ := by rfl
      rw [this]
      let k' (v : A) := (k.kernel i v : @Measure (Var → Val) ⊥)
      have {v : A} : k' v = (1 : MeasureOnSpace (Var → Val)).μ := by rfl
      have : (@μ.toMeasure A ⊤).bind k' = MeasureOnSpace.μ 1 := by aesop
      rw [this]
      trivial
    · apply Iris.BI.forall_intro
      intro v _ _ _
      trivial

-- ### C-FALSE

theorem C_False {A : Type*} {μ : PMF A} :
    (𝒞⟨μ⟩ _v; BFalse : bProp I Var Val) ⊢ BFalse := by
  unfold jointConditioning
  show entail _ _
  intro r _ hP
  obtain ⟨_, ⟨m, rfl⟩, h₁⟩ := hP
  obtain ⟨_, ⟨κ, rfl⟩, h₂⟩ := h₁
  obtain ⟨-, h_rest⟩ := h₂
  obtain ⟨-, h_carrier_all⟩ := h_rest
  obtain ⟨v₀, hv₀⟩ := PMF.support_nonempty μ
  exact h_carrier_all _ ⟨⟨v₀, hv₀⟩, rfl⟩

-- ### C-CONS

-- #### C-CONS: Helper lemmas

omit [Finite Var] [Countable Val] in
/-- The indexed probability space built from a compatible kernel at a fixed support point
is valid: each component is `some (...)` (hence not `⊤`), and its permission component
inherits validity from the underlying valid indexed space `m`. -/
private lemma jointConditioning_elem_valid {A : Type*}
    (m : ValidIndexedPSpPm I Var Val) (κ : CompatibleKernel A m) (v : A) :
    valid (fun i => (⟨⟨some ⟨⟨m.ms i, κ.kernel i v⟩, κ.isProb i v⟩, m.perm i⟩,
      κ.isComp i v⟩ : PSpPm Var Val)) := by
  intro i
  refine ⟨?_, (m.property i).2⟩
  exact Option.some_ne_none _

-- #### C-CONS: Spec & Proof

theorem C_Cons {α : Type} {K₁ K₂ : α → bProp I Var Val} {μ : PMF α} (h : ∀ v, K₁ v ⊢ K₂ v) :
    𝒞⟨μ⟩ v; K₁ v ⊢ 𝒞⟨μ⟩ v; K₂ v := by
  unfold jointConditioning
  show entail _ _
  intro r _ hP
  obtain ⟨_, ⟨m₀, rfl⟩, h₁⟩ := hP
  obtain ⟨_, ⟨κ, rfl⟩, h₂⟩ := h₁
  obtain ⟨h_own, h_bind_all, h_carrier_all⟩ := h₂
  refine ⟨_, ⟨m₀, rfl⟩, _, ⟨κ, rfl⟩, h_own, h_bind_all, ?_⟩
  intro p ⟨v, hv⟩
  subst hv
  exact h v _ (jointConditioning_elem_valid m₀ κ v) (h_carrier_all _ ⟨v, rfl⟩)

-- ### C-FRAME

theorem C_Frame {A : Type*} {μ : PMF A} {P : bProp I Var Val} {K : A → bProp I Var Val} :
  P ∗ 𝒞⟨μ⟩ v; K v ⊢ 𝒞⟨μ⟩ v; (P ∗ (K v)) := by
    sorry -- TODO: Rule C-FRAME proof (spec not yet reviewed)

-- ### C-UNIT-L

-- TODO: Rule C-UNIT-L (spec not yet reviewed)
theorem C_Unit_L {A : Type*} [Countable A] {v₀ : A} {K : A → bProp I Var Val} :
  𝒞⟨δ v₀⟩ _v; K v₀ ⊣⊢ K v₀ := by
    constructor
    · intro r _ hP
      obtain ⟨_, ⟨m₀, rfl⟩, h₁⟩ := hP
      obtain ⟨_, ⟨κ, rfl⟩, h₂⟩ := h₁
      obtain ⟨h_own, h_bind, h_carrier⟩ := h₂
      have hkey : ∀ i, κ.kernel i v₀ = m₀.μ i := by
        intro i
        have hb : m₀.μ i = @Measure.bind A (Var → Val) ⊤ (m₀.ms i)
            (@PMF.toMeasure A ⊤ (δ v₀)) (κ.kernel i) := h_bind _ ⟨i, rfl⟩
        rw [dirac_bind_top] at hb
        exact hb.symm
      have hpt : K v₀ (fun i => (⟨⟨some ⟨⟨m₀.ms i, κ.kernel i v₀⟩, κ.isProb i v₀⟩,
          m₀.perm i⟩, κ.isComp i v₀⟩ : PSpPm Var Val)) :=
        h_carrier _ ⟨⟨v₀, by simp⟩, rfl⟩
      have hval : (fun i => (⟨⟨some ⟨⟨m₀.ms i, κ.kernel i v₀⟩, κ.isProb i v₀⟩,
          m₀.perm i⟩, κ.isComp i v₀⟩ : PSpPm Var Val)) = m₀.val := by
        rw [← val_eq_point m₀]
        funext i
        simp only [hkey i]
      rw [hval] at hpt
      exact (K v₀).upper' h_own hpt
    · intro r hr hK
      refine ⟨_, ⟨⟨r, hr⟩, rfl⟩, _, ⟨CompatibleKernel.constSelf ⟨r, hr⟩, rfl⟩, ?_, ?_, ?_⟩
      · change (_ : IndexedPSpPm I Var Val) ≤ _; exact le_refl _
      · intro p hp; obtain ⟨i, rfl⟩ := hp
        exact (dirac_bind_top v₀ ((CompatibleKernel.constSelf (⟨r, hr⟩ :
          ValidIndexedPSpPm I Var Val)).kernel i)).symm
      · intro p hp; obtain ⟨⟨v, hv⟩, rfl⟩ := hp
        have hKr : K v₀ ((⟨r, hr⟩ : ValidIndexedPSpPm I Var Val).val) := hK
        rw [← val_eq_point (⟨r, hr⟩ : ValidIndexedPSpPm I Var Val)] at hKr
        exact hKr

-- ### C-UNIT-R

theorem C_Unit_R {A : Type*} {i : I} {μ : PMF A} {E : (Var → Val) → A} :
  E⟨i⟩ ~ μ ⊣⊢ 𝒞⟨μ⟩ v; ⌈(fun s ↦ E s = v)⟨i⟩⌉ := by
    sorry -- TODO: Rule C-UNIT-L proof (spec not yet reviewed)

-- ### C-ASSOC

theorem C_Assoc {A B : Type*} {μ : PMF A} {μ₀ : PMF (A × B)} {κ : A → PMF B} {K : (A × B) → bProp I Var Val} :
  μ₀ = (PMF.bind μ (λ v ↦ PMF.bind (κ v) (λ w ↦ PMF.pure (v, w)))) →
  𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K (v, w)
  ⊢ 𝒞⟨μ₀⟩ (v, w); K (v, w) := by
    sorry -- TODO: Rule C-ASSOC proof (spec not yet reviewed)

-- ### C-UNASSOC

-- TODO: Rule C-UNASSOC (spec not yet reviewed)
theorem C_Unassoc {A B : Type*} {μ : PMF A} {κ : A → PMF B} {K : B → bProp I Var Val} :
  𝒞⟨(PMF.bind μ κ)⟩ w; K w ⊢ 𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; K w := by
    intro r _ hP
    obtain ⟨_, ⟨m₀, rfl⟩, h₁⟩ := hP
    obtain ⟨_, ⟨κ₀, rfl⟩, h₂⟩ := h₁
    obtain ⟨h_own, h_bind, h_carrier⟩ := h₂
    refine ⟨_, ⟨m₀, rfl⟩, _, ⟨κ₀.pmfBind κ, rfl⟩, h_own, ?_, ?_⟩
    · intro p hp; obtain ⟨i, rfl⟩ := hp
      show m₀.μ i = _
      rw [h_bind _ ⟨i, rfl⟩]
      exact pmfBind_kernel_bind κ₀ μ κ i
    · intro p hp; obtain ⟨⟨v, hv⟩, rfl⟩ := hp
      refine ⟨_, ⟨⟨_, jointConditioning_elem_valid m₀ (κ₀.pmfBind κ) v⟩, rfl⟩, _,
        ⟨⟨fun i w => κ₀.kernel i w, fun i w => κ₀.isProb i w, fun i w => κ₀.isComp i w⟩, rfl⟩,
        ?_, ?_, ?_⟩
      · change (_ : IndexedPSpPm I Var Val) ≤ _; exact le_refl _
      · intro p hp; obtain ⟨i, rfl⟩ := hp; rfl
      · intro p hp; obtain ⟨⟨w, hw⟩, rfl⟩ := hp
        exact h_carrier _ ⟨⟨w, by rw [PMF.mem_support_bind_iff]; exact ⟨v, hv, hw⟩⟩, rfl⟩

-- ### C-AND

theorem C_And {A : Type*} {μ : PMF A} {K₁ K₂ : A → bProp I Var Val} :
  (∀ v, idx (K₁ v) ∩ idx (K₂ v) = ∅) →
  𝒞⟨μ⟩ v; (K₁ v) ∧ 𝒞⟨μ⟩ v; K₂ v ⊢ 𝒞⟨μ⟩ v; ((K₁ v) ∧ (K₂ v)) := by
    sorry -- TODO: Rule C-AND proof (spec not yet reviewed)

-- ### C-SKOLEM

-- TODO: Rule C-SKOLEM (spec not yet reviewed)
theorem C_Skolem {A X : Type*} {μ : PMF A} {Q : (A × X) → bProp I Var Val } :
  𝒞⟨μ⟩ v; (∃ x : X, Q (v, x)) ⊢ ∃ (f : A → X), 𝒞⟨μ⟩ v; Q (v, f v) := by
    intro r _ hP;
    obtain ⟨ _, ⟨ m0, rfl ⟩, h1 ⟩ := hP
    obtain ⟨ _, ⟨ κ, rfl ⟩, h2 ⟩ := h1
    obtain ⟨ h3, h4, h5 ⟩ := h2;
    obtain ⟨f, hf⟩ : ∃ f : A → X, ∀ v : A, v ∈ μ.support → Q (v, f v) (fun i => (⟨⟨some ⟨⟨m0.ms i, κ.kernel i v⟩, κ.isProb i v⟩, m0.perm i⟩, κ.isComp i v⟩ : PSpPm Var Val)) := by
      have h_exists_f : ∀ v ∈ μ.support, ∃ x : X, Q (v, x) (fun i => (⟨⟨some ⟨⟨m0.ms i, κ.kernel i v⟩, κ.isProb i v⟩, m0.perm i⟩, κ.isComp i v⟩ : PSpPm Var Val)) := by
        intro v hv;
        convert h5 _ ⟨ ⟨ v, hv ⟩, rfl ⟩ using 1;
        constructor <;> intro h;
        · exact h5 _ ⟨ ⟨ v, hv ⟩, rfl ⟩;
        · obtain ⟨ _, ⟨ x, rfl ⟩, hx ⟩ := h;
          exact ⟨ x, hx ⟩;
      by_cases hX : Nonempty X;
      · choose! f hf using h_exists_f;
        exact ⟨ f, hf ⟩;
      · obtain ⟨v, hv⟩ : ∃ v : A, v ∈ μ.support := by
          exact PMF.support_nonempty μ;
        exact False.elim ( hX <| by obtain ⟨ x, hx ⟩ := h_exists_f v hv; exact ⟨ x ⟩ );
    refine' ⟨ _, ⟨ f, rfl ⟩, _, ⟨ m0, rfl ⟩, _, ⟨ κ, rfl ⟩, h3, h4, _ ⟩;
    intro v;
    rintro ⟨ ⟨ v, hv ⟩, rfl ⟩;
    exact ( Q ( v, f v ) ).upper' ( le_rfl ) ( hf v hv )

-- ### C-TRANSF

-- #### C-TRANSF: Helper lemmas and helper definition

/-- Compose a CompatibleKernel with a function f : B → A -/
private def CompatibleKernel.comp {A B : Type*}
    {m₀ : ValidIndexedPSpPm I Var Val}
    (κ : CompatibleKernel A m₀) (f : B → A) : CompatibleKernel B m₀ where
  kernel i b := κ.kernel i (f b)
  isProb i b := κ.isProb i (f b)
  isComp i b := κ.isComp i (f b)

/-
Tsum over a PMF is invariant under a support-preserving bijection.
-/
private lemma PMF_tsum_comp_of_bijOn {A B : Type*} {μ : PMF A} {μ' : PMF B}
    {f : B → A}
    (h : A → ENNReal)
    (hbij : Set.BijOn f (μ' · ≠ 0) (μ · ≠ 0))
    (hprob : (∀ b : B, μ' b ≠ 0 → μ' b = μ (f b))) :
    ∑' a, μ a * h a = ∑' b, μ' b * h (f b) := by
  convert ( tsum_eq_tsum_of_ne_zero_bij _ _ _ _ );
  use fun x => f x;
  · exact fun x y hxy => Subtype.ext <| hbij.injOn ( by aesop ) ( by aesop ) hxy;
  · intro a ha;
    have := hbij.surjOn ( show a ∈ { a | μ a ≠ 0 } from by aesop ) ; aesop;
  · intros h₂
    rw [hprob]
    aesop

/-- The key measure-theoretic lemma: PMF.toMeasure.bind is invariant under
    a support-preserving bijection with matching probabilities. -/
private lemma PMF_bind_comp_of_bijOn {A B : Type*} {μ : PMF A} {μ' : PMF B}
    {f : B → A}
    {β : Type*} {mβ : MeasurableSpace β}
    (k : A → @Measure β mβ)
    (hbij : Set.BijOn f (μ' · ≠ 0) (μ · ≠ 0))
    (hprob : (∀ b : B, μ' b ≠ 0 → μ' b = μ (f b))) :
    @Measure.bind A β ⊤ mβ (@PMF.toMeasure A ⊤ μ) k =
    @Measure.bind B β ⊤ mβ (@PMF.toMeasure B ⊤ μ') (k ∘ f) := by
  letI instA : MeasurableSpace A := ⊤
  letI instB : MeasurableSpace B := ⊤
  haveI : MeasurableSingletonClass A := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : MeasurableSingletonClass B := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  -- PMF.toMeasure = sum of weighted Diracs
  have pmf_sum_A : PMF.toMeasure μ =
      Measure.sum (fun a => (μ a : ENNReal) • Measure.dirac a) := by
    ext s hs
    rw [PMF.toMeasure_apply μ hs, Measure.sum_apply _ hs]
    congr 1; ext a
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' a hs, Set.indicator]
    split_ifs <;> simp
  have pmf_sum_B : PMF.toMeasure μ' =
      Measure.sum (fun b => (μ' b : ENNReal) • Measure.dirac b) := by
    ext s hs
    rw [PMF.toMeasure_apply μ' hs, Measure.sum_apply _ hs]
    congr 1; ext b
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' b hs, Set.indicator]
    split_ifs <;> simp
  -- lintegral against PMF.toMeasure
  have pmf_lint_A : ∀ (g : A → ENNReal),
      ∫⁻ a, g a ∂(PMF.toMeasure μ) = ∑' a, μ a * g a := by
    intro g; rw [pmf_sum_A, MeasureTheory.lintegral_sum_measure]
    congr 1; ext a; rw [MeasureTheory.lintegral_smul_measure]; congr 1
    exact MeasureTheory.lintegral_dirac a g
  have pmf_lint_B : ∀ (g : B → ENNReal),
      ∫⁻ b, g b ∂(PMF.toMeasure μ') = ∑' b, μ' b * g b := by
    intro g; rw [pmf_sum_B, MeasureTheory.lintegral_sum_measure]
    congr 1; ext b; rw [MeasureTheory.lintegral_smul_measure]; congr 1
    exact MeasureTheory.lintegral_dirac b g
  -- Main proof
  ext s hs
  have haemA : AEMeasurable k (PMF.toMeasure μ) :=
    ⟨k, fun _ _ => MeasurableSpace.measurableSet_top, MeasureTheory.ae_eq_refl k⟩
  have haemB : AEMeasurable (k ∘ f) (PMF.toMeasure μ') :=
    ⟨k ∘ f, fun _ _ => MeasurableSpace.measurableSet_top, MeasureTheory.ae_eq_refl _⟩
  rw [Measure.bind_apply hs haemA, Measure.bind_apply hs haemB]
  rw [pmf_lint_A, pmf_lint_B]
  simp_rw [Function.comp_apply]
  exact PMF_tsum_comp_of_bijOn (fun a => (k a) s) hbij hprob

-- #### C-TRANSF: Spec & Proof

theorem C_Transf {A B : Type*}
  {μ : PMF A} {μ' : PMF B}
  {f : B → A}
  {K : A → bProp I Var Val} :
  Set.BijOn f (μ' · ≠ 0) (μ · ≠ 0) →
  (∀ b : B, μ' b ≠ 0 → μ' b = μ (f b)) →
    𝒞⟨μ⟩ a; K a ⊢ 𝒞⟨μ'⟩ b; K (f b)
:= by
  intro hbij hprob
  unfold jointConditioning
  show entail _ _
  intro r _ hP
  obtain ⟨_, ⟨m₀, rfl⟩, h₁⟩ := hP
  obtain ⟨_, ⟨κ, rfl⟩, h₂⟩ := h₁
  obtain ⟨h_own, h_rest⟩ := h₂
  obtain ⟨h_bind_all, h_carrier_all⟩ := h_rest
  have h_bind : ∀ i : I, m₀.μ i = κ.kernel i ∘ₘ (@PMF.toMeasure A ⊤ μ) := by
    intro i
    exact h_bind_all _ ⟨i, rfl⟩
  let κ' := κ.comp f
  refine ⟨_, ⟨m₀, rfl⟩, _, ⟨κ', rfl⟩, ?_⟩
  refine And.intro h_own (And.intro ?_ ?_)
  · intro p ⟨i, hi⟩
    subst hi
    change m₀.μ i = (κ.comp f).kernel i ∘ₘ (@PMF.toMeasure B ⊤ μ')
    rw [CompatibleKernel.comp, h_bind i]
    exact PMF_bind_comp_of_bijOn (κ.kernel i) hbij hprob
  · intro p ⟨v', hv'⟩
    subst hv'
    have hfv : μ (f v') ≠ 0 := hbij.mapsTo v'.property
    exact h_carrier_all _ ⟨⟨f v', hfv⟩, rfl⟩

-- ### SURE-STR-CONVEX

theorem Sure_Str_Convex {A : Type*} {μ : PMF A}
  {K : A → bProp I Var Val} {i : I} {E : (Var → Val) → Prop} :
    𝒞⟨μ⟩ v; (K v ∗ ⌈E⟨i⟩⌉) ⊢ ⌈E⟨i⟩⌉ ∗ 𝒞⟨μ⟩ v; K (v) := by
      sorry -- TODO: Rule SURE-STR-CONVEX proof

-- ### C-FOR-ALL

-- TODO: Rule C-FOR-ALL (spec not yet reviewed)
theorem C_For_All {A X : Type*} {μ : PMF A} {Q : (A × X) → bProp I Var Val} :
  𝒞⟨μ⟩ v; (∀ (x : X), Q (v, x)) ⊢ ∀ (x : X), 𝒞⟨μ⟩ v; Q (v, x) := by
    refine' fun m hv h => _;
    obtain ⟨ _, ⟨ m0, rfl ⟩, h1 ⟩ := h;
    obtain ⟨ _, ⟨ κ, rfl ⟩, h2 ⟩ := h1;
    obtain ⟨ h3, h4, h5 ⟩ := h2;
    intro x;
    rintro ⟨ a, rfl ⟩;
    refine' ⟨ _, ⟨ m0, rfl ⟩, _, ⟨ κ, rfl ⟩, h3, _, _ ⟩;
    · exact h4;
    · intro v;
      rintro ⟨ v, rfl ⟩;
      obtain ⟨ v, hv ⟩ := v;
      exact h5 _ ⟨ ⟨ v, hv ⟩, rfl ⟩ (Q (v, a)) ⟨ a, rfl ⟩

/- TODO: Confirm if the second `∀` should be a `iprop(∀ ...)` as it is now, or a regular `∀`.
         In the paper it is a bold ∀ (in the Latex it's `\A` rather than `\forall`).
         So I (Dan) think it should be `iprop(∀ ...)`.
         But just double-checking, since in the original formalisation (below) it was a regular `∀`.
-/

-- theorem C_forall {γ : Type*} {Q : β × γ → HyperAssertion I α V} :
--     𝑪_ μ (fun v => «forall» (fun x => Q (v, x))) ⊢ ∀ x, 𝑪_ μ (fun v => Q (v, x)) := by
--   sorry

-- ### C-PURE

theorem C_Pure {A : Type*} {X : Set A} {μ : PMF A} {K : A → bProp I Var Val} :
  ⌜ ∑' x : X, μ x = 1 ⌝ ∗ 𝒞⟨μ⟩ v; K v ⊣⊢ 𝒞⟨μ⟩ v; (⌜ v ∈ X ⌝ ∗ K v) := by
  constructor
  · intro r _ hsep
    obtain ⟨b₁, b₂, hle, hpure, hcond⟩ := hsep
    rw [pmf_tsum_subtype_eq_one_iff] at hpure
    obtain ⟨_, ⟨m, rfl⟩, h₂⟩ := hcond
    obtain ⟨_, ⟨κ, rfl⟩, h₃⟩ := h₂
    obtain ⟨h_own, h_bind, h_carrier⟩ := h₃
    refine ⟨_, ⟨m, rfl⟩, _, ⟨κ, rfl⟩, ?_, ?_, ?_⟩
    · show m.val ≤ r
      exact le_trans h_own (le_trans (IndexedPSpPm.le_of_mul_right I Val Var) hle)
    · intro p hp; obtain ⟨i, rfl⟩ := hp; exact h_bind _ ⟨i, rfl⟩
    · intro p hp; obtain ⟨v, rfl⟩ := hp
      exact ⟨1, _, (one_mul _).le, hpure v v.2, h_carrier _ ⟨v, rfl⟩⟩
  · intro r hr hcond
    obtain ⟨_, ⟨m, rfl⟩, h₂⟩ := hcond
    obtain ⟨_, ⟨κ, rfl⟩, h₃⟩ := h₂
    obtain ⟨h_own, h_bind, h_carrier⟩ := h₃
    have hsupp : ∀ v, v ∈ μ.support → v ∈ X := by
      intro v hv
      obtain ⟨c₁, c₂, hcle, hc1, hc2⟩ := h_carrier _ ⟨⟨v, hv⟩, rfl⟩
      exact hc1
    refine ⟨1, r, (one_mul r).le, ?_, ?_⟩
    · show ∑' x : X, μ x = 1
      rw [pmf_tsum_subtype_eq_one_iff]; exact hsupp
    · refine ⟨_, ⟨m, rfl⟩, _, ⟨κ, rfl⟩, h_own, ?_, ?_⟩
      · intro p hp; obtain ⟨i, rfl⟩ := hp; exact h_bind _ ⟨i, rfl⟩
      intro p hp; obtain ⟨v, rfl⟩ := hp
      obtain ⟨c₁, c₂, hcle, hc1, hc2⟩ := h_carrier _ ⟨v, rfl⟩
      exact (K v).upper' (le_trans (IndexedPSpPm.le_of_mul_right I Val Var) hcle) hc2

-- # The primitive WP rules of Bluebell (see Fig. 10)

-- ## Structural WP rules

-- ### WP-CONS

theorem WP_Cons
  (t : I → Option (PSpPm Var Val → PSpPm Var Val))
  (Q Q' : bProp I Var Val) (hQ : Q ⊢ Q')
  : wp t Q ⊢ wp t Q' := by
  intro m _ hm μ₀ c hvμ₀ hmul
  obtain ⟨b, hbc, hvb, hQb⟩ := hm μ₀ c hvμ₀ hmul
  exact ⟨b, hbc, hvb, hQ b hvb hQb⟩

-- ### WP-FRAME

theorem WP_Frame
  (t : I → Option (PSpPm Var Val → PSpPm Var Val))
  (ht : ∀ μ, ✓ μ → ✓ (⟦t⟧ μ))
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
  have hb_c' : (a₁ * b₀) * c' ≤ ⟦t⟧ μ₀ :=
    calc (a₁ * b₀) * c'
        = (b₀ * a₁) * c' := by rw [mul_comm a₁ b₀]
      _ = b₀ * (a₁ * c') := mul_assoc _ _ _
      _ ≤ ⟦t⟧ μ₀ := hb₀c
  have hvab : ✓ (a₁ * b₀) := valid_mul (valid_mono hb_c' (ht μ₀ hvμ₀))
  exact ⟨a₁ * b₀, hb_c', hvab, a₁, b₀, le_refl _, hPa₁, hQb₀⟩

-- ### WP-NEST

open Classical in
theorem WP_Nest
  {t₁ t₂ : I → Option (PSpPm Var Val → PSpPm Var Val)}
  {Q : bProp I Var Val}
  (h_no_overlap : (dom t₁) ∩ (dom t₂) = ∅) :
  -- The dot notation between hyper-terms t₁ and t₂, takes its definition from section 2.2 of the LHC (OOPSLA22) paper, https://doi.org/10.1145/3563298 (page 5).
  let t₁_dot_t₂ : I → Option (PSpPm Var Val → PSpPm Var Val) := (fun i : I =>
    if h_t₁ : (t₁ i).isSome
    then
      if h_t₂ : (t₂ i).isSome
      then
        (by
          exfalso -- This case is unreachable due to `h_no_overlap`. So we first replace the goal with `False`, then show the contradiction. This avoids having to use a "dummy" value here (such as `.none`).
          unfold dom hyperTermReferences at h_no_overlap
          have : i ∈ {x | (t₁ x).isSome = true} ∩ {x | (t₂ x).isSome = true} := by
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
            aesop
          aesop
        )
      else t₁ i
    else
      t₂ i
  )
  wp t₁ (wp t₂ Q) ⊣⊢ wp (t₁_dot_t₂) Q := by
    sorry -- TODO: Rule WP-NEST proof (spec not yet reviewed)

-- ### WP-CONJ

open Classical in
theorem WP_Conj
    (t₁ t₂ : I → Option (PSpPm Var Val → PSpPm Var Val))
    {Q₁ Q₂ : bProp I Var Val}
    (h_ts_agree : ∀ i : I, i ∈ dom t₁ ∩ dom t₂ → t₁ i = t₂ i)
     :
    -- The plus notation between hyper-terms t₁ and t₂, takes its definition from section 2.2 of the LHC (OOPSLA22) paper, https://doi.org/10.1145/3563298 (page 5).
    let t₁_plus_t₂ : I → Option (PSpPm Var Val → PSpPm Var Val) := (fun i : I =>
      match h_t₁ : t₁ i with
      | .some t₁_i =>
        match h_t₂ : t₂ i with
        | .some t₂_i =>
          if h_eq : t₁_i = t₂_i
            then t₁_i
            else (
              by
                exfalso -- This case is unreachable due to `h_ts_agree`. So we first replace the goal with `False`, then show the contradiction. This avoids having to use a "dummy" value here (such as `.none`).
                unfold dom hyperTermReferences at *
                have := h_ts_agree i
                aesop
              )
        | .none => .some t₁_i
      |.none =>
        match t₂ i with
        | .some t₂_i => .some t₂_i
        | .none => .none)
    (idx Q₁) ∩ dom t₂ ⊆ dom t₁ →
    (idx Q₂) ∩ dom t₁ ⊆ dom t₂ →
    wp t₁ Q₁ ∧ wp t₂ Q₂ ⊢ wp t₁_plus_t₂ iprop(Q₁ ∧ Q₂) := by
    sorry -- TODO: Rule WP-CONJ proof

-- ### C-WP-SWAP

-- New variant of CP-WP-SWAP
theorem C_WP_Swap {A : Type*} [Countable A]
  {μ : PMF A}
  {t : I → Option (PSpPm Var Val → PSpPm Var Val)}
  {Q : A → bProp I Var Val} {i : I} {E : (Var → Val) → A}
  :
  𝒞⟨μ⟩ v; (⌈(fun s => E s = v)⟨i⟩⌉ ∗ wp t (Q v)) ⊢ wp t (𝒞⟨μ⟩ v; (⌈(fun s => E s = v)⟨i⟩⌉ ∗ Q v)) := by
    sorry -- TODO: Rule C-WP-SWAP proof (spec not yet reviewed)

-- ## Program WP rules

-- TODO: Shallow embedding

-- ### WP-SKIP

-- TODO: Rule WP-SKIP spec+proof

-- ### WP-SEQ

-- TODO: Rule WP-SEQ spec+proof

-- ### WP-ASSIGN

-- TODO: Rule WP-ASSIGN spec+proof

-- ### WP-SAMP

-- TODO: Rule WP-SAMP spec+proof

-- ### WP-IF-PRIM

-- TODO: Rule WP-IF-PRIM spec+proof

-- ### WP-BIND

-- TODO: Rule WP-BIND spec+proof

-- ### WP-LOOP-UNF

-- TODO: Rule WP-LOOP-UNF spec+proof

-- ### WP-LOOP

-- TODO: Rule WP-LOOP spec+proof

-- # Derived (non-WP) rules (see Fig. 11)

-- ## Ownership and distributions

-- ### SURE-DIRAC

omit [Finite Var] [Countable Val] in
theorem Sure_Dirac
  {A : Type*} [Countable A] [DecidableEq A] {E : (Var → Val) → A} {i : I} {v : A}
  : E⟨i⟩ ~ δ v ⊣⊢ ⌈(fun s ↦ E s = v)⟨i⟩⌉ := by
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
    letI : MeasurableSpace Prop := ⊤
    have hg : @Measurable A Prop ⊤ ⊤ (fun a => a = v) := fun _ _ => trivial
    have bridge_E : @Measure.map _ _ (P.ms i) ⊤ E (P.μ i)
        = @Measure.map _ _ (P.PSpace i).1.ms ⊤ E (P.PSpace i).1.μ :=
      ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ E
    rw [bridge_E] at hμ
    constructor
    · refine ⟨(fun a => a = v) ∘ E', hg.comp hE'_meas, ?_⟩
      exact hE'_ae.fun_comp (fun a => a = v)
    · have bridge_prop : @Measure.map _ _ (P.ms i) ⊤ (fun s => E s = v) (P.μ i)
          = @Measure.map _ _ (P.PSpace i).1.ms ⊤ (fun s => E s = v)
              (P.PSpace i).1.μ :=
        ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ _
      rw [bridge_prop]
      apply @Measure.ext _ ⊤
      intro s hs
      have ham_E : AEMeasurable E (P.PSpace i).1.μ := ⟨E', hE'_meas, hE'_ae⟩
      have ham_p : AEMeasurable (fun x => E x = v) (P.PSpace i).1.μ := by
        refine ⟨(fun a => a = v) ∘ E', hg.comp hE'_meas, ?_⟩
        exact hE'_ae.fun_comp (fun a => a = v)
      rw [Measure.map_apply_of_aemeasurable (mβ := ⊤) ham_p hs]
      change (P.PSpace i).1.μ (E ⁻¹' ((fun a => a = v) ⁻¹' s)) = _
      rw [← Measure.map_apply_of_aemeasurable (mβ := ⊤) ham_E
            MeasurableSpace.measurableSet_top, hμ]
      change PMF.toDiscMeasure (δ v) _ = PMF.toDiscMeasure (δ True) _
      simp only [PMF.dirac, PMF.toDiscMeasure, Measure.toPMF_toMeasure,
        Measure.dirac_apply', MeasurableSpace.measurableSet_top]
      classical
      simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  · intro m hv h
    obtain ⟨q, ⟨P, hqP⟩, hqm⟩ := h
    subst hqP
    obtain ⟨b₁, b₂, hle, hown, body⟩ := hqm
    refine ⟨_, ⟨P, rfl⟩, b₁, b₂, hle, hown, ?_⟩
    simp only [almostMeasurable, ValidIndexedPSpPm.PSp, ValidPSpPm.PSp] at body
    obtain ⟨ham, hμ⟩ := body
    letI : MeasurableSpace A := ⊤
    letI : MeasurableSpace Prop := ⊤
    have bridge_prop : @Measure.map _ _ (P.ms i) ⊤ (fun s => E s = v) (P.μ i)
        = @Measure.map _ _ (P.PSpace i).1.ms ⊤ (fun s => E s = v)
            (P.PSpace i).1.μ :=
      ValidPSpPm.map_μ_eq_map_PSpace_μ ⟨P.val i, P.property i⟩ _
    rw [bridge_prop] at hμ
    simp only [ValidIndexedPSpPm.PSpace] at hμ
    have h_null : (P.PSpace i).1.μ {s | ¬ E s = v} = 0 := by
      have h1 := Measure.map_apply_of_aemeasurable ham (s := {False}) MeasurableSpace.measurableSet_top
      rw [hμ] at h1
      simp only [PMF.dirac, Measure.toPMF_toMeasure,
        MeasurableSpace.measurableSet_top, Measure.dirac_apply'] at h1
      have hTF : (True : Prop) ∉ ({False} : Set Prop) := by
        intro h; exact (Set.mem_singleton_iff.mp h).mp trivial
      rw [Set.indicator_of_notMem hTF] at h1
      rw [show (P.PSpace i).1.μ {s | ¬E s = v}
          = (P.PSpace i).1.μ ((fun x => E x = v) ⁻¹' {False}) from by
        congr 1; ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
          eq_iff_iff, iff_false]]
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
          (by simp_all only [PSp.compatiblePerm, OrderedUnitalResourceAlgebra.instValidForall.eq_1, ValidPSpPm.PSpace,
            ValidPSpPm, ValidPSp.PSpace, ValidPSp, PMF.dirac, Measure.toPMF_toMeasure, ValidIndexedPSpPm.ms,
            ValidPSpPm.ms, ValidPSp.ms, ValidIndexedPSpPm.μ, ValidPSpPm.μ, ValidPSp.μ, ValidIndexedPSpPm.PSpace,
            MeasurableSpace.measurableSet_top, Measure.dirac_apply', Set.indicator_of_mem, Pi.one_apply])
      · rw [Set.preimage_const_of_notMem hv_s, MeasureTheory.measure_empty]
        simp only [PMF.dirac, Measure.toPMF_toMeasure, Measure.dirac_apply', MeasurableSpace.measurableSet_top]
        exact (Set.indicator_of_notMem hv_s _).symm

-- ### SURE-EQ-INJ

omit [Finite Var] [Countable Val] in
theorem Sure_Eq_Inj {A : Type*} {i : I} [DecidableEq A]
  {E : (Var → Val) → A}
  {v v' : A} :
  ⌈(fun s => E s = v)⟨i⟩⌉ ∗ ⌈(fun s => E s = v')⟨i⟩⌉
  ⊢ ⌜ v = v' ⌝ := by
    intro m hm; simp +decide [ * ] ;
    intro hsep
    obtain ⟨b₁, b₂, hle, h1, h2⟩ := hsep
    set M : ValidIndexedPSpPm I Var Val := ⟨m, hm⟩
    set a1 : ∀ᵐ s ∂(M.PSpace i).1.μ, E s = v := by
      apply almostSurely_ae M;
      exact ( almostSurely _ i ).upper' ( le_trans ( IndexedPSpPm.le_of_mul_left I Val Var ) hle ) h1
    set a2 : ∀ᵐ s ∂(M.PSpace i).1.μ, E s = v' := by
      generalize_proofs at *;
      apply almostSurely_ae;
      exact ( almostSurely _ i ).upper' ( le_trans ( IndexedPSpPm.le_of_mul_right I Val Var ) hle ) h2;
    generalize_proofs at *;
    have hvv : ∀ᵐ s ∂(M.PSpace i).1.μ, v = v' := by
      filter_upwards [ a1, a2 ] with s hs1 hs2 using hs1.symm.trans hs2;
    haveI : IsProbabilityMeasure (M.PSpace i).1.μ := (M.PSpace i).2;
    exact hvv.exists.choose_spec

-- ### SURE-SUB

omit [Finite Var] [Countable Val] in
theorem Sure_Sub {A B: Type*} {i : I}
  {E₁ : (Var → Val) → A} {E₂ : (Var → Val) → B}
  {μ : PMF A}
  {f : A → B}
  :
  let prf : HasSum (fun b => ∑' (a : ↑(f ⁻¹' {b})), μ ↑a) 1 := (by exact pmf_pushforward_hasSum μ f)
  E₁⟨i⟩ ~ μ ∗ ⌈(fun s => E₂ s = f (E₁ s))⟨i⟩⌉
  ⊢ E₂⟨i⟩ ~ (⟨fun b ↦ ∑' a : f ⁻¹' {b}, μ a, prf⟩)
  := by
    intro prf
    show E₁⟨i⟩ ~ μ ∗ ⌈(fun s => E₂ s = f (E₁ s))⟨i⟩⌉
      ⊢ E₂⟨i⟩ ~ (⟨fun b ↦ ∑' a : f ⁻¹' {b}, μ a, pmf_pushforward_hasSum μ f⟩)
    letI : MeasurableSpace A := ⊤
    letI : MeasurableSpace B := ⊤
    intro m hm hsep
    obtain ⟨b₁, b₂, hle, hE₁, hsure⟩ := hsep
    set M : ValidIndexedPSpPm I Var Val := ⟨m, hm⟩ with hM
    have hE₁m : (E₁⟨i⟩ ~ μ) m :=
      (hasDistribution E₁ i μ).upper'
        (le_trans (IndexedPSpPm.le_of_mul_left I Val Var) hle) hE₁
    have hsurem : (⌈(fun s => E₂ s = f (E₁ s))⟨i⟩⌉) m :=
      (almostSurely (fun s => E₂ s = f (E₁ s)) i).upper'
        (le_trans (IndexedPSpPm.le_of_mul_right I Val Var) hle) hsure
    obtain ⟨hae₁P, hmap₁⟩ := hasDistribution_elim M hE₁m
    have hae₁ : @AEMeasurable _ _ ⊤ (M.ms i) E₁ (M.μ i) :=
      (ValidIndexedPSpPm.aemeasurable_PSpace_iff_μ M i).1 hae₁P
    have hae_eq' : E₂ =ᵐ[M.μ i] (fun s => f (E₁ s)) :=
      (ValidIndexedPSpPm.ae_PSpace_iff_μ M i).1 (almostSurely_ae M hsurem)
    apply hasDistribution_intro M
    · exact (measurable_from_top.comp_aemeasurable hae₁).congr hae_eq'.symm
    · have hmm : @Measure.map _ _ (M.ms i) ⊤ (fun s => f (E₁ s)) (M.μ i)
          = @Measure.map A B ⊤ ⊤ f (@Measure.map (Var → Val) A (M.ms i) ⊤ E₁ (M.μ i)) :=
        (AEMeasurable.map_map_of_aemeasurable measurable_from_top.aemeasurable hae₁).symm
      rw [pushforward_eq_map, ← PMF.toMeasure_map f μ measurable_from_top,
        Measure.map_congr hae_eq', hmm, hmap₁]

-- ### DIST-FUN

omit [Finite Var] [Countable Val] in
theorem Dist_Fun {i : I} {A B: Type*}
  {E : (Var → Val) → A}
  {μ : PMF A}
  {f : A → B}
  :
  let prf : HasSum (fun b => ∑' (a : ↑(f ⁻¹' {b})), μ ↑a) 1 := (by exact pmf_pushforward_hasSum μ f)
  E⟨i⟩ ~ μ ⊢ (fun s => (f ∘ E) s)⟨i⟩ ~ (⟨fun b ↦ ∑' a : f ⁻¹' {b}, μ a, prf⟩)
  := by
    intro prf
    show E⟨i⟩ ~ μ ⊢ (fun s => (f ∘ E) s)⟨i⟩ ~ (⟨fun b ↦ ∑' a : f ⁻¹' {b}, μ a, pmf_pushforward_hasSum μ f⟩)
    intro m hm h
    obtain ⟨q, ⟨P, rfl⟩, hpm⟩ := h
    obtain ⟨b₁, b₂, hle, hown, hbody⟩ := hpm
    obtain ⟨p, ⟨a, rfl⟩, hsome⟩ := hown
    obtain ⟨ham, hμ⟩ := hbody
    letI : MeasurableSpace A := ⊤
    letI : MeasurableSpace B := ⊤
    refine ⟨_, ⟨P, rfl⟩, b₁, b₂, hle, ⟨_, ⟨a, rfl⟩, hsome⟩, ?_, ?_⟩
    · exact Measurable.comp_aemeasurable measurable_from_top ham
    · rw [pushforward_eq_map, ← PMF.toMeasure_map f μ measurable_from_top, ← hμ,
        ValidIndexedPSpPm.map_μ_eq_map_PSpace_μ P i (fun s => (f ∘ E) s),
        ValidIndexedPSpPm.map_μ_eq_map_PSpace_μ P i E]
      exact (AEMeasurable.map_map_of_aemeasurable (g := f) (f := E)
        measurable_from_top.aemeasurable ham).symm

-- ### DIRAC-DUP

theorem Dirac_Dup
  {A : Type*} [Countable A]
  {E : (Var → Val) → A} (i : I) (v : A)
  :   E⟨i⟩ ~ δ v
    ⊢ E⟨i⟩ ~ δ v ∗ E⟨i⟩ ~ δ v := by
  classical
  intro m hv h
  -- 🤖: Convert the dirac distribution to a sure assertion.
  have h1 : (⌈(fun s => E s = v)⟨i⟩⌉) m := Sure_Dirac.mp m hv h
  -- 🤖: Duplicate the sure assertion via `Sure_Merge` (backward), using that the
  --     self-conjunction predicate `E s = v ∧ E s = v` is just `E s = v`.
  have hpred : (fun s => E s = v ∧ E s = v) = (fun s => E s = v) := by
    funext s; simp
  have h2 := (Sure_Merge (A := Unit) (E₁ := fun s => E s = v)
      (E₂ := fun s => E s = v) (i := i)).mpr m hv (by rw [hpred]; exact h1)
  obtain ⟨b₁, b₂, hle, hb₁, hb₂⟩ := h2
  have hvb₁ : valid b₁ :=
    valid_mono (le_trans (IndexedPSpPm.le_of_mul_left I Val Var) hle) hv
  have hvb₂ : valid b₂ :=
    valid_mono (le_trans (IndexedPSpPm.le_of_mul_right I Val Var) hle) hv
  exact ⟨b₁, b₂, hle, Sure_Dirac.mpr b₁ hvb₁ hb₁, Sure_Dirac.mpr b₂ hvb₂ hb₂⟩


-- ### DIST-SUPP

theorem Dist_Supp {i : I} {A : Type*}
  {E : (Var → Val) → A}
  {μ : PMF A}
  :
  E⟨i⟩ ~ μ ⊢ E⟨i⟩ ~ μ ∗ ⌈(fun s => E s ∈ μ.support)⟨i⟩⌉ := by
    sorry -- TODO: Rule DIRAC-SUPP proof

-- ### PROD-UNSPLIT

theorem Prod_Unsplit {A B : Type*} {i : I}
  {μ₁ : PMF A} {μ₂ : PMF B}
  {E₁ : (Var → Val) → A} {E₂ : (Var → Val) → B} :
  E₁⟨i⟩ ~ μ₁ ∗ E₂⟨i⟩ ~ μ₂
  ⊢ (fun s => (E₁ s, E₂ s))⟨i⟩ ~ (μ₁ ⊗ μ₂) := by
    sorry -- TODO: Rule PROD-UNSPLIT proof

-- ## Joint conditioning

-- ### C-FUSE

-- #### C-FUSE: Helper definition

def fusion {A B : Type*} (μ : PMF A) (κ : A → PMF B) : PMF (A × B) :=
  let prf : HasSum (fun (v, w) => μ v * (κ v) w) 1 := (by
    have h : ∑' (p : A × B), μ p.1 * (κ p.1) p.2 = 1 := by
      simp_rw [ENNReal.tsum_prod', ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one,
        PMF.tsum_coe]
    convert h ▸ ENNReal.summable.hasSum)
  (⟨fun (v, w) => (μ v) * ((κ v) w), prf⟩)

-- #### C-FUSE: Spec & Proof

theorem C_Fuse {A B : Type*} {μ : PMF A} {κ : A → PMF B} {K : (A × B) → bProp I Var Val} :
  𝒞⟨μ⟩ v; 𝒞⟨κ v⟩ w; (K (v, w)) ⊣⊢ 𝒞⟨fusion μ κ⟩ (v, w); K (v, w) := by
    sorry -- TODO: Rule C-FUSE proof (spec not yet reviewed)

-- ### C-SWAP

theorem C_Swap {A B : Type*} {μ₁ : PMF A} {μ₂ : PMF B} (K : (A × B) → bProp I Var Val) :
  𝒞⟨μ₁⟩ v₁; 𝒞⟨μ₂⟩ v₂; K (v₁, v₂) ⊢ 𝒞⟨μ₂⟩ v₂; 𝒞⟨μ₁⟩ v₁; K (v₁, v₂) := by
    sorry -- TODO: Rule C-SWAP proof (spec not yet reviewed)


-- ### SURE-CONVEX

-- #### SURE-CONVEX: Helper lemmas

omit [Finite Var] [Countable Val] [DecidableEq Var] [Inhabited Val] in
/-- If an event-complement `{s | ¬ E s}` is null under every kernel in the support of a
PMF, then it is null under the `bind`. Handles the fact that `{s | ¬ E s}` need not be
measurable by passing to a countable intersection of measurable null supersets. -/
private lemma bind_event_null {A : Type*}
    {ms : MeasurableSpace (Var → Val)}
    (μ : PMF A) (κ : A → @Measure (Var → Val) ms)
    (E : (Var → Val) → Prop)
    (h : ∀ a : μ.support, (κ a) {s | ¬ E s} = 0) :
    (@Measure.bind A (Var → Val) ⊤ ms (@PMF.toMeasure A ⊤ μ) κ) {s | ¬ E s} = 0 := by
  -- Let $N$ be the intersection of $N_v$ for all $v \in \text{supp}(\mu)$.
  obtain ⟨N, hN_meas, hN_sub, hN_zero⟩ : ∃ N : Set (Var → Val), MeasurableSet N ∧ {s | ¬E s} ⊆ N ∧ ∀ v : μ.support, (κ v) N = 0 := by
    revert h;
    intro h
    have h_countable_support : Countable μ.support := by
      exact μ.support_countable.to_subtype;
    have hN : ∀ v : μ.support, ∃ N_v : Set (Var → Val), MeasurableSet N_v ∧ {s | ¬E s} ⊆ N_v ∧ (κ v) N_v = 0 := by
      intro v;
      have := MeasureTheory.exists_measurable_superset_of_null ( h v ) ; aesop;
    choose N hN_meas hN_sub hN_zero using hN;
    refine' ⟨ ⋂ v : μ.support, N v, MeasurableSet.iInter hN_meas, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
    exact fun a ha => MeasureTheory.measure_mono_null ( Set.iInter_subset_of_subset a ( Set.iInter_subset _ ha ) ) ( hN_zero a ha );
  refine MeasureTheory.measure_mono_null hN_sub ?_
  rw [MeasureTheory.Measure.bind_apply hN_meas measurable_from_top.aemeasurable]
  rw [MeasureTheory.lintegral_eq_zero_iff (by fun_prop)]
  convert PMF.toMeasure_apply_eq_zero_iff _ _ |>.2 ?_
  · simp +decide
  · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂ <| hN_zero ⟨x, hx₁⟩

-- #### SURE-CONVEX: Spec & Proof

theorem Sure_Convex {A : Type*}
  {μ : PMF A}
  {i : I} {E : (Var → Val) → Prop}
  :
  𝒞⟨μ⟩ _v; ⌈E⟨i⟩⌉ ⊢ ⌈E⟨i⟩⌉ := by
    intro r _ hP
    obtain ⟨_, ⟨m, rfl⟩, h₁⟩ := hP
    obtain ⟨_, ⟨κ, rfl⟩, h₂⟩ := h₁
    obtain ⟨h_own, h_bind_all, h_carrier_all⟩ := h₂
    apply (almostSurely E i).upper' h_own
    apply almostSurely_intro m
    rw [MeasureTheory.ae_iff]
    have key := bind_event_null μ (κ.kernel i) E
      (fun v => MeasureTheory.ae_iff.mp
        (almostSurely_ae ⟨_, jointConditioning_elem_valid m κ v⟩ (h_carrier_all _ ⟨v, rfl⟩)))
    rw [← ValidIndexedPSpPm.mu_apply_eq_PSpace m i, h_bind_all _ ⟨i, rfl⟩]
    exact key

-- ### DIST-CONVEX

theorem Dist_Convex {A : Type*}
  {μ μ' : PMF A}
  {i : I} {E : (Var → Val) → A}
  :
  𝒞⟨μ⟩ v; E⟨i⟩ ~ μ' ⊢ E⟨i⟩ ~ μ' := by
    intro r _ hP
    obtain ⟨_, ⟨m, rfl⟩, h₁⟩ := hP
    obtain ⟨_, ⟨κ, rfl⟩, h₂⟩ := h₁
    obtain ⟨h_own, h_bind_all, h_carrier_all⟩ := h₂
    apply (hasDistribution E i μ').upper' h_own
    have hae : ∀ v : μ.support, @AEMeasurable _ _ ⊤ (m.ms i) E (κ.kernel i v) := by
      intro v
      have := (hasDistribution_elim (⟨_, jointConditioning_elem_valid m κ v⟩)
        (h_carrier_all _ ⟨v, rfl⟩)).1
      exact (ValidIndexedPSpPm.aemeasurable_PSpace_iff_μ
        (⟨_, jointConditioning_elem_valid m κ v⟩) i).1 this
    have hmap : ∀ v : μ.support,
        @Measure.map _ _ (m.ms i) ⊤ E (κ.kernel i v) = @PMF.toMeasure A ⊤ μ' := by
      intro v
      exact (hasDistribution_elim (⟨_, jointConditioning_elem_valid m κ v⟩)
        (h_carrier_all _ ⟨v, rfl⟩)).2
    refine ⟨_, ⟨m, rfl⟩, m.val, 1, (mul_one _).le, ownPSp_self m, ?_, ?_⟩
    · show almostMeasurable E (m.PSp i)
      rw [show m.PSp i = some (m.PSpace i) from rfl]
      show @AEMeasurable _ _ ⊤ (m.PSpace i).1.ms E (m.PSpace i).1.μ
      rw [ValidIndexedPSpPm.aemeasurable_PSpace_iff_μ m i, h_bind_all _ ⟨i, rfl⟩]
      exact aemeasurable_pmf_bind μ (κ.kernel i) E hae
    · show @Measure.map _ _ (m.ms i) ⊤ E (m.μ i) = @PMF.toMeasure A ⊤ μ'
      rw [h_bind_all _ ⟨i, rfl⟩]
      exact map_pmf_bind_const μ (κ.kernel i) E _ hae hmap

-- ### C-SURE-PROJ

theorem C_Sure_Proj {A B : Type*} {i : I} {μ : PMF (A × B)} {E : A → (Var → Val) → Prop}
  :
  let prf : HasSum (fun a => ∑' (b : B), μ (a, b)) 1 := (by rw [ENNReal.summable.hasSum_iff, ← ENNReal.tsum_prod]; exact μ.2.tsum_eq)
  𝒞⟨μ⟩ (v, _); ⌈(E v)⟨i⟩⌉ ⊣⊢ 𝒞⟨⟨(fun a ↦ ∑' b, (μ (a, b))), prf⟩⟩ v; (⌈(E v)⟨i⟩⌉) := by
    sorry -- TODO: Rule C-SURE-PROJ proof (spec not yet reviewed)

-- ### C-SURE-PROJ-MANY

theorem C_Sure_Proj_Many {A B : Type*} {i : I} {X : Set (I × Var)} {μ : PMF ((X → Val) × B)} :
  let prf : HasSum (fun a => ∑' (b : B), μ (a, b)) 1 := (by rw [ENNReal.summable.hasSum_iff, ← ENNReal.tsum_prod]; exact μ.2.tsum_eq)
  𝒞⟨μ⟩ (v, w); (∀ (ix : X), ⌈(fun (s : Var → Val) => s ix.1.2 = v ix)⟨ix.1.1⟩⌉)
  ⊣⊢ 𝒞⟨⟨(fun a ↦ ∑' b, (μ (a, b))), prf⟩⟩ v; (∀ (ix : X), ⌈(fun (s : Var → Val) => s ix.1.2 = v ix)⟨ix.1.1⟩⌉) := by
    sorry -- TODO: Rule C-SURE-PROJ-MANY proof (spec not yet reviewed)

-- ### C-EXTRACT

theorem C_Extract {A B : Type*}
  {μ₁ : PMF A} {μ₂ : PMF B}
  {i : I}
  {E₁ : (Var → Val) → A} {E₂ : (Var → Val) → B}
  :
  𝒞⟨μ₁⟩ v₁; (⌈(fun s => E₁ s = v₁)⟨i⟩⌉ ∗ E₂⟨i⟩ ~ μ₂)
  ⊢ E₁⟨i⟩ ~ μ₁ ∗ E₂⟨i⟩ ~ μ₂ := by
    sorry -- TODO: Rule C-EXTRACT proof

-- ### C-DIST-PROJ

/--
The Bluebell paper has a typo in C-DIST-PROJ.
In the paper's rendition of the rule, the `μ` in the modality and the one in the assertion are meant to be different variables.
In other words, in the paper, both occurences of `μ(x)` should not be the same `μ` as the two subscript `μ`s following `𝒞`.
This is why we have `μ₁` and `μ₂` here.
-/
theorem C_Dist_Proj {A B C : Type*} {μ₁ : PMF (A × B)} {μ₂ : A → (PMF C)} {i : I} {E : A → (Var → Val) → C} :
  let prf : HasSum (fun a => ∑' (b : B), μ₁ (a, b)) 1 := (by rw [ENNReal.summable.hasSum_iff, ← ENNReal.tsum_prod]; exact μ₁.2.tsum_eq)
  𝒞⟨μ₁⟩ (x, y); (E x)⟨i⟩ ~ μ₂ x ⊢ 𝒞⟨⟨(fun a ↦ ∑' b, (μ₁ (a, b))), prf⟩⟩ x; (E x)⟨i⟩ ~ (μ₂ x) := by
    sorry -- TODO: Rule C-DIST-PROJ proof (spec not yet reviewed)

-- ## Relational lifting

-- ### Helper definition

def relationalLifting {X : Set (I × Var)} (R : Set (X → Val)) : bProp I Var Val :=
  iprop(∃ μ : PMF (X → Val),
      ⌜ ∑' r : R, μ r = 1 ⌝ ∗
      𝒞⟨μ⟩ v; ∀ (ix : X), ⌈(fun (s : Var → Val) => s ix.1.2 = v ix)⟨ix.1.1⟩⌉
    )

notation " ⌊ " R " ⌋ " => relationalLifting R

-- ### RL-CONS

theorem RL_Cons {X : Set (I × Var)} {R₁ R₂ : Set (X → Val)} :
    R₁ ⊆ R₂ → ⌊R₁⌋ ⊢ ⌊R₂⌋ := by
  intro hR₁R₂ r hv h;
  obtain ⟨μ, hμ⟩ := h;
  obtain ⟨ ⟨ μ, rfl ⟩, hμ ⟩ := hμ;
  obtain ⟨ b₁, b₂, hle, hpure, hcond ⟩ := hμ;
  have h_sum_le : ∑' r : R₁, μ r ≤ ∑' r : R₂, μ r := by
    rw [tsum_subtype, tsum_subtype]
    exact ENNReal.tsum_le_tsum
      (Set.indicator_le_indicator_of_subset hR₁R₂ (fun _ => zero_le _))
  have h_sum_le_one : ∑' r : R₂, μ r ≤ 1 := by
    have h_sum_le_one : ∑' r : R₂, μ r ≤ ∑' r : X → Val, μ r := by
      rw [ tsum_subtype ];
      apply ENNReal.tsum_le_tsum;
      intro a; by_cases ha : a ∈ R₂ <;> simp +decide [ ha ] ;
    exact h_sum_le_one.trans ( by simp +decide [ PMF.tsum_coe ] );
  refine' ⟨ _, ⟨ μ, rfl ⟩, b₁, b₂, hle, _, hcond ⟩;
  have h_sum_eq_one : ∑' r : R₁, μ r = 1 := hpure
  exact le_antisymm h_sum_le_one (h_sum_eq_one ▸ h_sum_le)

-- ### RL-UNARY

open Classical in
theorem RL_Unary {X : Set Var} [Finite X] {R : Set (X → Val)}
  {i : I}
  :
  let X' : Set (I × Var)  := X.image (i,·)
  let R' : Set (X' → Val) :=
    R.image
      (fun s x ↦ s ⟨x.1.2, by aesop⟩)
  ⌊R'⌋ ⊢ ⌈(fun σ ↦ ∃ σ' ∈ R, ∀ v : X, σ v.1 = σ' v)⟨i⟩⌉ := by
    simp only [relationalLifting]
    sorry -- TODO: Rule RL-UNARY proof

-- ### RL-EQ-DIST

theorem RL_Eq_Dist {A : Type*} [Inhabited A] [Inhabited X] {X : Set (I × Var)} {μ : PMF A} {ix jy : X} :
  ix.1.1 ≠ jy.1.1 →
  ⌊{v : (X → Val) | v ix = v jy}⌋
  ⊢ iprop(∃ μ, ((fun _ ↦ ix.1.2))⟨ix.1.1⟩ ~ μ ∗ ((fun _ => jy.1.2))⟨jy.1.1⟩ ~ μ) := by
    sorry -- TODO: Rule RL-EQ-DIST proof (spec not yet reviewed)


-- ### RL-CONVEX

theorem RL_Convex {α : Type} {X : Set (I × Var)} {μ : PMF α} {R : Set (X → Val)} :
  𝒞⟨μ⟩ v; ⌊R⌋ ⊢ ⌊R⌋ := by
    sorry -- TODO: Rule RL-CONVEX proof

-- ### RL-MERGE

theorem RL_Merge {X : Set (I × Var)} {R₁ R₂ : Set (X → Val)} :
  ⌊R₁⌋ ∗ ⌊R₂⌋ ⊢ ⌊ R₁ ∩ R₂ ⌋ := by
    sorry -- TODO: Rule RL-SURE-MERGE proof

-- ### RL-SURE-MERGE

open Classical in
theorem RL_Sure_Merge {X : Set (I × Var)} {R : Set (X → Val)} {e : (Var → Val) → Val}
  {i : I} {x : Var}
  :
  pvar e ⊆ {var : Var | (i, var) ∈ X}
  → ⌊R⌋ ∗ ⌈(fun s => s x = e s)⟨i⟩⌉ ⊢
  ⌊R ∩ {v |
      let s : Var → Val :=
        fun x' => if h : (i, x') ∈ X then v ⟨(i, x'), h⟩ else default
      s x = e s
    }⌋ := by
      sorry -- TODO: Rule RL-SURE-MERGE proof

-- ### COUPLING

open Classical in
theorem Coupling
    {i₁ i₂ : I} {x₁ x₂ : Var} {R : Set (({(i₁, x₁), (i₂, x₂)} : Set (I × Var)) → Val)}
    {μ₁ μ₂ : PMF Val} {μ : PMF (({(i₁, x₁), (i₂, x₂)} : Set (I × Var)) → Val)}
    (h : i₁ ≠ i₂)
    (h₁ : (fun v ↦ ∑' σ : {σ : (({(i₁, x₁), (i₂, x₂)} : Set (I × Var)) → Val) | σ ⟨(i₁, x₁), by simp⟩ = v}, μ σ) = μ₁)
    (h₂ : (fun v ↦ ∑' σ : {σ : (({(i₁, x₁), (i₂, x₂)} : Set (I × Var)) → Val) | σ ⟨(i₂, x₂), by simp⟩ = v}, μ σ) = μ₂)
    (hR : ∑' σ : R, μ σ.1 = 1)
  : (fun s ↦ s x₁)⟨i₁⟩ ~ μ₁ ∗ (fun s ↦ s x₂)⟨i₂⟩ ~ μ₂ ⊢ ⌊ R ⌋ := by
    sorry -- TODO: Rule COUPLING proof

-- # Derived WP rules (see Fig. 12)

-- TODO: Shallow embedding

-- ### WP-LOOP-0

-- TODO: Rule WP-LOOP-0 spec+proof

-- ### WP-LOOP-LOCKSTEP

-- TODO: Rule WP-LOOP-LOCKSTEP spec+proof

-- ### WP-RL-ASSIGN

-- TODO: Rule WP-RL-ASSIGN spec+proof

-- ### WP-IF-UNARY

-- TODO: Rule WP-IF-UNARY spec+proof

end BluebellRules

end Formula

end Bluebell
