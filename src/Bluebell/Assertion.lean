import Iris.BI.BIBase
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Set.Basic
import Bluebell.DiscreteCMRA
import Bluebell.MeasureOnSpace
import Iris.BI.BIBase
import Iris.Algebra.UPred

open ProbabilityTheory MeasureTheory

namespace Bluebell

variable {I Var Val : Type*} [DecidableEq Var] [Inhabited Val]

abbrev Assertion (M : Type*) [OrderedUnitalResourceAlgebra M] :=
  UpperSet M

@[simp]
def bProp (I Var Val : Type*) [DecidableEq Var] [Inhabited Val] :=
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

end ValidIndexedPSpPm

noncomputable section PMF

@[simp]
def PMF.dirac {A : Type*} [Countable A] (x : A) : PMF A :=
  @Measure.toPMF A _ ⊤ _ (@Measure.dirac A ⊤ x) _

@[simp]
def PMF.toDiscMeasure {A : Type*} [Countable A] (μ : PMF A) : @Measure A ⊤ :=
  @μ.toMeasure A ⊤

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

notation:30 "⊢ " P => entail BTrue P
notation:30 P " ⊢ " Q => entail P Q
notation:30 P " ⊣⊢ " Q => bientail P Q
notation:40 "∀'" K => bforall K
notation:40 "∃'" K => bexists K
notation:60 P:60 " ∧' " Q:60 => and P Q
notation:60 P " ∨' " Q => or P Q
notation:70 P:70 " *' " Q:71 => sep P Q
notation:80 "↑ " φ:80 => lift φ

structure IxCompatiblePermission (P : I → PSp (Var → Val)) where
  perm : I → Permission Var
  comp : ∀ i, (P i).compatiblePerm (perm i)

def ownIndexedPSpPm (P : I → PSp (Var → Val)) (p : IxCompatiblePermission P)
  : bProp I Var Val :=
  own (fun i ↦ ⟨⟨P i, p.perm i⟩, p.comp i⟩) ∧' ↑ (∀ i : I, (P i).isSome)

def ownPSp (P : I → PSp (Var → Val)) : bProp I Var Val :=
  ∃' (fun p : IxCompatiblePermission P => ownIndexedPSpPm P p)

def almostMeasurable {A : Type*} (E : (Var → Val) → A) (P : PSp (Var → Val)) : Prop :=
  match P with
  | none => False
  | some p => @AEMeasurable (Var → Val) A ⊤ _ E p.1.μ

def hasDistribution {A : Type*} (E : (Var → Val) → A) (i : I) (μ : PMF A)
  : bProp I Var Val :=
  ∃' (fun P : ValidIndexedPSpPm I Var Val =>
    ownPSp P.PSp *' lift (
      let μᵢ := P.μ i
      have Eμᵢ := @μᵢ.map (Var → Val) A (P.ms i) ⊤ E
      almostMeasurable E (P.PSp i)
      ∧ Eμᵢ = @μ.toMeasure A ⊤)
  )

notation:100 E:100 "⟨" i:100 "⟩" " ~ " p:100 => hasDistribution E i p

noncomputable def almostSurely (E : (Var → Val) → Bool) (i : I) : bProp I Var Val :=
  E⟨i⟩ ~ PMF.dirac True

def ownRV {A : Type*} (E : (Var → Val) → A) (i : I) : bProp I Var Val :=
  ∃' (fun μ : PMF A => E⟨i⟩ ~ μ)

def cond {A : Type*} (μ : PMF A) (K : A → bProp I Var Val) [Countable (Var → Val)]
  : bProp I Var Val :=
  ∃' (fun m : ValidIndexedPSpPm I Var Val =>
    own m.val ∧'
      (∀' (fun i : I => ↑ ((m.μ i).toPMF = (do { let x ← μ; return _ })))) ∧'
        (∀' (fun v : μ.support => ↑ (sorry ∈ (K v).carrier))))

theorem EDistInj
  {A : Type*} {E : (Var → Val) → A} {i : I} {μ μ' : PMF A}
  : E⟨i⟩ ~ μ ∧' E⟨i⟩ ~ μ' ⊢ ↑(μ = μ') := by
  sorry
/-
theorem EDistInj
  {A : Type*} {E : (Var → Val) → A} {i : I} {μ μ' : PMF A}
  : E⟨i⟩ ~ μ ∧' E⟨i⟩ ~ μ' ⊢ ↑(μ = μ') := by
  intro m hv h
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨P, b₁, b₂, hle, ⟨p, hpown, hsome⟩, body⟩ := h₁
  obtain ⟨P', b₁', b₂', hle', ⟨p', hpown', hsome'⟩, body'⟩ := h₂
  simp only [lift] at body body'
  obtain ⟨ham, hμ₁⟩ := body
  obtain ⟨ham', hμ₂⟩ := body'
  have hv_i : ✓ (m i) := hv i
  have hmi_ne_top : (m i).1.1 ≠ ⊤ := hv_i.1
  match hmi : (m i).1.1 with
  | none => contradiction
  | some y =>
  have hPi_le_m :=
    le_trans (hpown i).1 (le_trans PSp.le_of_mul_left (hle i).1)
  have hP'i_le_m :=
    le_trans (hpown' i).1 (le_trans PSp.le_of_mul_left (hle' i).1)
  rw [hmi] at hPi_le_m hP'i_le_m
  have hxy : P i ≤ y := by cases hPi_le_m; assumption
  have hx'y : P' i ≤ y := by cases hP'i_le_m; assumption
  rw [← hμ₁, ← hμ₂]
  ext u hu
  rw [Measure.map_apply_of_aemeasurable ham hu,
      Measure.map_apply_of_aemeasurable ham' hu]
  set f := AEMeasurable.mk E ham
  set f' := AEMeasurable.mk E ham'
  have hf_meas : @Measurable _ _ (P i).1.ms _ f := by measurability
  have hf'_meas : @Measurable _ _ (P' i).1.ms _ f' := by measurability
  have hf_ae : f =ᵐ[(P i).1.μ] E := (AEMeasurable.ae_eq_mk ham).symm
  have hf'_ae : f' =ᵐ[(P' i).1.μ] E := (AEMeasurable.ae_eq_mk ham').symm
  have h1 : (P i).1.μ (E ⁻¹' u) = (P i).1.μ (f ⁻¹' u) :=
    measure_congr (hf_ae.symm.preimage u)
  have h3 : (P' i).1.μ (E ⁻¹' u) = (P' i).1.μ (f' ⁻¹' u) :=
    measure_congr (hf'_ae.symm.preimage u)
  have h2 : (P i).1.μ (f ⁻¹' u) = y.1.μ (f ⁻¹' u) :=
    MeasureOnSpace.le_preserves_measure hxy (hf_meas hu)
  have h4 : (P' i).1.μ (f' ⁻¹' u) = y.1.μ (f' ⁻¹' u) :=
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
  rw [h1, h2, h5, ← h4, ← h3]

theorem EDiracDup
  {A : Type*} [Countable A]
  {E : (Var → Val) → A} (i : I) (v : A)
  :   (E⟨i⟩ ~ PMF.dirac v)
    ⊢ (E⟨i⟩ ~ PMF.dirac v *' E⟨i⟩ ~ PMF.dirac v) := by
  sorry

theorem EProdSplit
  {A B : Type*} [Countable A] [Countable B]
  {E₁ : (Var → Val) → A} {E₂ : (Var → Val) → B} {i : I}
  {μ₁ : PMF A} {μ₂ : PMF B}
  :   (fun s => (⟨E₁ s, E₂ s⟩ : A × B))⟨i⟩ ~ μ₁ * μ₂
    ⊢ E₁⟨i⟩ ~ μ₁ *' E₂⟨i⟩ ~ μ₂ := by
  sorry
-/

end Formula

section Properties

theorem sep_ident {P : bProp I Var Val}
  : P *' BTrue ⊣⊢ P := by
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
  : P *' Q ⊣⊢ Q *' P := by
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
  : (P *' Q) *' R ⊣⊢ P *' (Q *' R) := by
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

end Properties

end Bluebell
