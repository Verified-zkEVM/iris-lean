import Bluebell.MeasureOnSpace
import Mathlib.Probability.ProbabilityMassFunction.Basic

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
  coe_injective := by intro P Q h; aesop

instance : FunLike (bProp I Var Val) (IndexedPSpPm I Var Val) Prop where
  coe := fun P => P.carrier
  coe_injective := by intro P Q h; aesop

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
  -- Equiv φ ψ := bientail φ ψ
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
  eq_dist := by
    intros x y
    unfold bientail entail
    simp_all only [bProp, forall_const]
    apply Iff.intro
    · intro a
      subst a
      simp_all only [implies_true, and_self]
    · intro a
      obtain ⟨left, right⟩ := a
      ext m
      have : ✓m := by
        sorry
      aesop
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
  eq_dist := sorry -- ⟨fun h _ => h, fun h => h 0⟩
  dist_lt := fun h _ => h
  compl := fun h => h 0
  conv_compl := by
    intro n c
    unfold Iris.Chain.chain
    unfold bientail
    have a := @c.cauchy (n := 0) (i := n) (Nat.zero_le n)
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
    sorry
    -- intro P Q
    -- constructor
    -- · rintro ⟨h₁, h₂⟩
    --   refine ⟨?_, ?_⟩
    --   assumption; assumption
    -- · rintro ⟨h₁, h₂⟩
    --   refine ⟨?_, ?_⟩
    --   assumption; assumption
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
      exact ⟨PSp.le_of_mul_right, by intro x; exact le_add_of_nonneg_left (zero_le)⟩
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

end Formula

end Bluebell
