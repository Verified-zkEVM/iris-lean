import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! ## Independent product of probability measures -/

open ProbabilityTheory MeasureTheory

alias MeasureTheory.MeasureSpace.σAlg := MeasureSpace.toMeasurableSpace
alias MeasureTheory.MeasureSpace.μ := MeasureSpace.volume

variable {Ω : Type*}
         {α β : Type*}

noncomputable section

namespace MeasureTheory

abbrev Measure.map! (ms₁ : MeasurableSpace α) (ms₂ : MeasurableSpace β)
                    (f : α → β) (μ : Measure α) : Measure β := @μ.map _ _ ms₁ ms₂ f

abbrev Measure.cast {β : Type u} {ms₁ : MeasurableSpace β}
  (μ : Measure β) (ms₂ : MeasurableSpace β) := μ.map! ms₁ ms₂ id

@[simp]
lemma Measure.cast_eq_self {β : Type u} {ms₁ : MeasurableSpace β}
  (μ : Measure β) (ms₂ : MeasurableSpace β) : μ.cast ms₂ = @μ.map _ _ ms₁ ms₂ id := rfl

-- an induction principle with respect to the trivial σ-algebra
-- to show that a property P u holds where u is a measurable set
-- with respect to the trivial σ-algebra, it suffices to show that
-- P ∅ and P Ω

lemma MeasurableSet.measurableSet_bot_induction
  {P : Set Ω → Prop}
  (h_base : P ∅) (h_ind : P Set.univ)
  : (u : Set Ω) → MeasurableSet[⊥] u → P u := by
  intro u h_u
  have : u = ∅ ∨ u = Set.univ := by
    apply MeasurableSpace.measurableSet_bot_iff.1 h_u
  grind

end MeasureTheory

@[simp]
def MeasurableSpace.sum (m₁ : MeasurableSpace Ω) (m₂ : MeasurableSpace Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom (MeasurableSet[m₁] ∪ MeasurableSet[m₂])

def MeasurableSpace.cast
  (m₁ m₂ : MeasurableSpace Ω) (p : m₁ = m₂) (E : Set Ω) (h : MeasurableSet[m₁] E) :
  MeasurableSet[m₂] E := by
  subst p
  simp_all only

end noncomputable section

section Sum

@[simp]
def MeasurableSpace.sumUnit : MeasurableSpace Ω := ⊥

lemma MeasurableSpace.sum_identity {m : MeasurableSpace Ω}
  : MeasurableSpace.sum sumUnit m = m := by
  let f : Set (Set Ω) := MeasurableSet[sumUnit]
  let g : Set (Set Ω) := MeasurableSet[m]
  have : f ∪ g = g := by
    ext u
    simp
    unfold f
    intro hu
    apply MeasurableSet.measurableSet_bot_induction
    apply MeasurableSet.empty
    apply MeasurableSet.univ
    aesop
  simp
  have h : MeasurableSpace.generateFrom (f ∪ g) = MeasurableSpace.generateFrom g := by
    grind
  have : MeasurableSpace.generateFrom MeasurableSet[m] = m := by
    apply MeasurableSpace.generateFrom_measurableSet
  aesop

lemma MeasurableSpace.sum_comm {m n : MeasurableSpace Ω}
  : m.sum n = n.sum m := by
  let f : Set (Set Ω) := MeasurableSet[m]
  let g : Set (Set Ω) := MeasurableSet[n]
  unfold MeasurableSpace.sum
  have : f ∪ g = g ∪ f := by
    ext u
    grind
  grind

lemma MeasurableSpace.sum_le {m₁ m₂ : MeasurableSpace Ω}
  : m₁ ≤ m₁.sum m₂ := by
  simp
  intro u hu
  sorry

lemma MeasurableSpace.sum_assoc {m₁ m₂ m₃ : MeasurableSpace Ω}
  : (m₁.sum m₂).sum m₃ = m₁.sum (m₂.sum m₃) := by
  let f : Set (Set Ω) := MeasurableSet[m₁]
  let g : Set (Set Ω) := MeasurableSet[m₂]
  let h : Set (Set Ω) := MeasurableSet[m₃]
  sorry

end Sum

/- We define `(𝓕, μ) ≤ (𝓖, ν)` if `𝓕 ⊆ 𝓖` and `μ` is the restriction of `ν` to `𝓕` -/
@[ext]
structure MeasureOnSpace (Ω : Type*) where
  ms : MeasurableSpace Ω
  μ : Measure[ms] Ω

instance (Ω : Type*) : Preorder (MeasureOnSpace Ω) where
  le (ps₁ ps₂) := ps₁.ms ≤ ps₂.ms ∧ ps₁.μ = ps₂.μ.cast _
  le_refl := by simp
  le_trans (h₁ h₂) := by
    aesop (add safe forward le_trans) (add safe (by rw [MeasureTheory.Measure.map_map]))

def PSpace (Ω : Type*) :=
  {m : MeasureOnSpace Ω // IsProbabilityMeasure m.μ}

instance (Ω : Type*) : Preorder (PSpace Ω) where
  le (ps₁ ps₂) := (ps₁.1.ms ≤ ps₂.1.ms) ∧ ps₁.1.μ = ps₂.1.μ.cast _
  le_refl := by simp
  le_trans {a b c} (h₁ h₂) := by
    aesop (add safe forward le_trans) (add safe (by rw [MeasureTheory.Measure.map_map]))

abbrev PSp (Ω : Type*) := WithTop (PSpace Ω)

/-- Holds if `r` is the independent product of `p` and `q` -/
def PSpace.isIndependentProduct (r p q : PSpace Ω) :=
  r.1.ms = p.1.ms.sum q.1.ms ∧
  letI μ₁ := p.1.μ
  letI μ₂ := q.1.μ
  letI μ := r.1.μ
  ∀ E (_ : MeasurableSet[p.1.ms] E)
    F (_ : MeasurableSet[q.1.ms] F),
  μ (E ∩ F) = μ₁ E * μ₂ F

lemma PSpace.isIndependentProduct_def {r p q : PSpace Ω} :
  isIndependentProduct r p q ↔
  r.1.ms = p.1.ms.sum q.1.ms ∧
  ∀ E (_ : MeasurableSet[p.1.ms] E)
    F (_ : MeasurableSet[q.1.ms] F),
  r.1.μ (E ∩ F) = p.1.μ E * q.1.μ F := Iff.rfl

open PSpace

lemma PSpace.ms_eq_of_isIndependentProduct {r r' p q : PSpace Ω}
  (h₁ : isIndependentProduct r p q) (h₂ : isIndependentProduct r' p q) :
  r.1.ms = r'.1.ms := by
  rcases h₁ with ⟨a, _⟩
  rcases h₂ with ⟨c, _⟩
  aesop

section GeneratingPiSystem

variable {Ω : Type*} (p q : MeasureOnSpace Ω)

/--
  Given `p q : MeasureOnSpace Ω`, `generator p q` is a set of subsets of Ω that
  generates the smallest σ-algebra containing both σ-algebras
-/
def generator (p q : MeasureOnSpace Ω) : Set (Set Ω) :=
  {S : Set Ω | ∃ F G, S = F ∩ G ∧ MeasurableSet[p.ms] F ∧ MeasurableSet[q.ms] G}

section

variable {p q : MeasureOnSpace Ω}
         {u v w : Set Ω}

/-- Every set in the generating set `w` is of the form `u ∩ v` -/
lemma exists_inter_measurableSet_of_mem_generator (hw : w ∈ generator p q) :
  ∃ u v, w = u ∩ v ∧ MeasurableSet[p.ms] u ∧ MeasurableSet[q.ms] v := by
  rcases hw with ⟨u, v, rfl, hu, hv⟩
  grind

@[aesop 50% apply]
lemma mem_generator_l (hu : MeasurableSet[p.ms] u) :
  u ∈ generator p q := by
  use u, ⊤
  aesop

@[aesop 50% apply]
lemma mem_generator_r (hu : MeasurableSet[q.ms] u) :
  u ∈ generator p q := by
  use ⊤, u
  aesop

lemma inter_mem_generator
  (hu : MeasurableSet[p.ms] u) (hv : MeasurableSet[q.ms] v) :
  u ∩ v ∈ generator p q := by
  use u, v

lemma mem_generator_imp_mem_sum (h : u ∈ generator p q)
  : MeasurableSet[p.ms.sum q.ms] u := by
  sorry

end

attribute [local aesop safe apply] MeasurableSpace.measurableSet_generateFrom

theorem MeasureOnSpace.generateFrom_generator_eq_sum :
  MeasurableSpace.generateFrom (generator p q) = p.ms.sum q.ms := by
  ext s
  refine ⟨?p, by apply MeasurableSpace.generateFrom_mono (fun _ _ ↦ by aesop)⟩
  let sumSp := MeasurableSet[p.ms.sum q.ms]
  apply MeasurableSpace.generateFrom_le
  rintro t ⟨u, ⟨v, _, _, _⟩⟩
  have h₂ : generator p q ⊆ sumSp := fun u hu ↦ by
    obtain ⟨u₁, v₁, rfl, _, _⟩ := exists_inter_measurableSet_of_mem_generator hu
    exact (show sumSp u₁ by aesop).inter (by aesop)
  apply MeasurableSpace.generateFrom_le (by convert h₂)
  aesop (add simp (show u ∩ v ∈ generator p q by use u, v))

lemma MeasureOnSpace.isPiSystem_generator : IsPiSystem (generator p q) := fun _ hu _ hv _ ↦ by
  obtain ⟨_, _, rfl, _, _⟩ := exists_inter_measurableSet_of_mem_generator hu
  obtain ⟨_, _, rfl, _, _⟩ := exists_inter_measurableSet_of_mem_generator hv
  rw [Set.inter_inter_inter_comm]
  aesop (add safe apply inter_mem_generator)

end GeneratingPiSystem

section Uniqueness

lemma MeasurableSpace.eq_cast_ext_ext
  {m₁ m₂ : MeasurableSpace Ω}
  (μ : Measure[m₁] Ω) (ν : Measure[m₂] Ω)
  (h_eq : m₁ = m₂) (h₂ : ∀ w, MeasurableSet[m₁] w → μ w = ν w) :
  μ = ν.cast _ := by aesop

@[ext]
lemma MeasureOnSpace.ext_ms {p q : MeasureOnSpace Ω}
  (h_eq_alg : p.ms = q.ms)
  (h_eq_mea : ∀ E, MeasurableSet[p.ms] E → p.μ E = q.μ E) :
  p = q := by
  aesop (add safe cases MeasureOnSpace)

@[ext]
lemma PSpace.ext_ms {p q : PSpace Ω}
  (h_eq_alg : p.1.ms = q.1.ms)
  (h_eq_mea : ∀ E, MeasurableSet[p.1.ms] E → p.1.μ E = q.1.μ E) : p = q := by
  rcases p with ⟨a, _⟩
  rcases q with ⟨b, _⟩
  have : a = b := MeasureOnSpace.ext_ms h_eq_alg h_eq_mea
  aesop

@[simp, grind .]
lemma PSpace.measure_ne_top {m : PSpace Ω} {u : Set Ω} : m.1.μ u ≠ ⊤ := by
  apply ne_of_lt
  have h₁ : m.1.μ Set.univ = 1 := m.2.measure_univ
  have h₂ : u ⊆ Set.univ := by aesop
  have h₃ : m.1.μ u ≤ m.1.μ Set.univ := measure_mono h₂
  exact lt_of_le_of_lt (b := 1) (by aesop) (by aesop)

theorem PSpace.uniqueness {r r' p q : PSpace Ω}
  (h₁ : isIndependentProduct r p q) (h₂ : isIndependentProduct r' p q) : r = r' := by
  apply PSpace.ext_ms (h₁.1 ▸ h₂.1 ▸ rfl)
  -- have : IsPiSystem (generator p.1 q.1) := MeasureOnSpace.isPiSystem_generator p.1 q.1
  -- Applying the π-λ theorem: the σ-algebra is by definition a λ-system,
  -- so we just need to show that the measures agree on a generating π-system
  rw [PSpace.isIndependentProduct_def] at h₁ h₂
  apply MeasurableSpace.induction_on_inter
  · exact MeasureOnSpace.isPiSystem_generator p.1 q.1
  · simp
  · intro t ht
    obtain ⟨u, v, rfl, hu, hv⟩ := exists_inter_measurableSet_of_mem_generator ht
    grind
  · aesop (add simp MeasureTheory.measure_compl) (add safe cases PSpace)
  · intro us disjoint hus prf
    have h_sum1 : r.1.μ (⋃ i, us i) = ∑' i, r.1.μ (us i) :=
      @Measure.m_iUnion (α := Ω) (f := us) r.1.ms r.1.μ hus disjoint
    have : r'.1.μ (⋃ i, us i) = ∑' i, r'.1.μ (us i) :=
      @Measure.m_iUnion (α := Ω) (f := us) r'.1.ms r'.1.μ (by aesop) disjoint
    aesop
  · aesop (add simp MeasureOnSpace.generateFrom_generator_eq_sum)

end Uniqueness

section Trim

@[simp]
def MeasureOnSpace.trim
  {p : MeasureOnSpace Ω} {f : MeasurableSpace Ω} (h : f ≤ p.ms)
  : MeasureOnSpace Ω := {
  ms := f
  μ := p.μ.trim h
}

lemma MeasureOnSpace.trim_eq
  {p : MeasureOnSpace Ω} {f : MeasurableSpace Ω} (h : f ≤ p.ms)
  {u : Set Ω} (hu : MeasurableSet[f] u)
  : (p.trim h).μ u = p.μ u := by
  have h₁ := (p.trim h).μ.trim_eq hu
  have h₂ : (p.trim h).μ.toOuterMeasure u = p.μ u := by
    sorry
  rw [h₂] at h₁
  aesop

@[simp]
def PSpace.trim
  {p : PSpace Ω} {f : MeasurableSpace Ω} {h : f ≤ p.1.ms}
  : PSpace Ω := ⟨p.1.trim h, by
  simp
  constructor
  have : (p.1.trim h).μ Set.univ = 1 := by
    sorry
  aesop
⟩

end Trim

section Identity

lemma dirac_is_prob [Inhabited Ω] : IsProbabilityMeasure (@Measure.dirac Ω ⊥ default) := by
  apply isProbabilityMeasure_iff.2
  simp

def unit [Inhabited Ω] : PSpace Ω := ⟨{
  ms := ⊥
  μ := @Measure.dirac Ω ⊥ default
}, dirac_is_prob⟩

lemma empty_sigma_algebra_is_identity [Inhabited Ω] (p : MeasureOnSpace Ω)
  : p.ms = MeasurableSpace.generateFrom (unit.1.ms.MeasurableSet' ∪ p.ms.MeasurableSet') := by
  let a : Set (Set Ω) := p.ms.MeasurableSet'
  let b : Set (Set Ω) := unit.1.ms.MeasurableSet'
  have h : a = b ∪ a := by
    ext u
    constructor
    grind
    simp
    intro h
    rcases h with h1 | h2
    apply MeasurableSet.measurableSet_bot_induction
    unfold a
    apply MeasurableSpace.measurableSet_empty
    have : Set.univ ∈ a := by
      unfold a
      apply MeasurableSet.univ
    assumption
    assumption
    assumption
  rw [← h]
  have : p.ms = MeasurableSpace.generateFrom (p.ms.MeasurableSet') := by
    have := @MeasurableSpace.generateFrom_measurableSet Ω p.ms
    grind
  assumption

theorem indepenendentProduct_identity [Inhabited Ω] {p : PSpace Ω}
  : isIndependentProduct p unit p := by
  unfold isIndependentProduct
  constructor
  simp
  ext u
  have : p.1.ms = MeasurableSpace.generateFrom (unit.1.ms.MeasurableSet' ∪ p.1.ms.MeasurableSet') :=
    empty_sigma_algebra_is_identity p.1
  constructor
  apply MeasurableSpace.cast
  assumption
  apply MeasurableSpace.cast
  apply Eq.symm
  assumption
  let μ := p.1.μ
  let ν : Measure[⊥] Ω := unit.1.μ
  intro u h_u v h_v
  let P u := μ (u ∩ v) = unit.1.μ u * μ v
  apply MeasurableSet.measurableSet_bot_induction (P := P)
  unfold P
  simp
  unfold P
  simp_all
  have h : ν Set.univ = 1 := by
    apply unit.2.measure_univ
  rw [h]
  grind
  apply h_u

end Identity

section Commutativity

theorem independentProduct_comm [Inhabited Ω] {r p q : PSpace Ω}
  (h : isIndependentProduct r p q)
  : isIndependentProduct r q p := by
  constructor
  have h₁ : MeasurableSpace.sum p.1.ms q.1.ms
    = MeasurableSpace.sum q.1.ms p.1.ms := by
    apply MeasurableSpace.sum_comm
  have : r.1.ms = MeasurableSpace.sum p.1.ms q.1.ms := h.1
  grind
  intro u hu v hv
  let μ := r.1.μ
  let μ₁ := q.1.μ
  let μ₂ := p.1.μ
  have : μ (v ∩ u) = μ₂ v * μ₁ u := h.2 v hv u hu
  grind

end Commutativity

section Associativity

-- Recall the definiton of partial associativity (Kleene equality):
--  (a * b) * c ≃ a * (b * c) means:
-- If (a * b) and (a * b) * c are defined then
--   1. (b * c) and a * (b * c) are defined
--   2. (a * b) * c = a * (b * c)
-- The above definition suffices because we proved commutativity
theorem independentProduct_assoc {pq p q s r : PSpace Ω} [Inhabited Ω]
  (h_pq : isIndependentProduct pq p q)
  (h_pq_r : isIndependentProduct s pq r)
  : ∃ qr, isIndependentProduct qr q r ∧ isIndependentProduct s p qr
  := by
  let qr_ms : MeasurableSpace Ω := MeasurableSpace.sum q.1.ms r.1.ms
  have h : qr_ms <= s.1.ms := by sorry
  let qr : PSpace Ω := @s.trim Ω qr_ms h
  have h_qr : isIndependentProduct qr q r := by
    constructor
    simp
    aesop
    intro u hu v hv
    have hou : MeasurableSet[pq.1.ms] (Set.univ ∩ u) := by
      simp
      have h : pq.1.ms = p.1.ms.sum q.1.ms := h_pq.1
      rw [h]
      have h₂ : u ∈ generator p.1 q.1 := mem_generator_r hu
      apply @mem_generator_imp_mem_sum Ω p.1 q.1 u h₂
    have h := h_pq_r.2 (Set.univ ∩ u) hou v hv
    have h₁ : pq.1.μ (Set.univ ∩ u) = q.1.μ u := by
      have := h_pq.2 Set.univ MeasurableSet.univ u hu
      have : p.1.μ Set.univ = 1 := p.2.measure_univ
      aesop
    have h₂ : s.1.μ (Set.univ ∩ u ∩ v) = qr.1.μ (u ∩ v) := by
      have := h_pq_r.2 (Set.univ ∩ u) hou v hv
      have h₃ : s.1.μ (Set.univ ∩ u ∩ v) = pq.1.μ (Set.univ ∩ u) * r.1.μ v := by
        grind
      have h₄ : pq.1.μ (Set.univ ∩ u) = p.1.μ Set.univ * q.1.μ u :=
        h_pq.2 Set.univ MeasurableSet.univ u hu
      rw [h₄] at h₃
      have h₅ : p.1.μ Set.univ = 1 := p.2.measure_univ
      rw [h₅] at h₃
      unfold qr
      apply Eq.symm
      have h₇ : MeasurableSet[q.1.ms.sum r.1.ms] (u ∩ v) := by
        apply mem_generator_imp_mem_sum
        apply inter_mem_generator hu hv
      have h₈ : q.1.ms.sum r.1.ms ≤ s.1.ms := sorry
      have := @s.1.trim_eq Ω (q.1.ms.sum r.1.ms) h₈ (u ∩ v) h₇
      have : s.1.μ (Set.univ ∩ u ∩ v) = s.1.μ (u ∩ v) := by
        have : Set.univ ∩ u ∩ v = u ∩ v := by grind
        aesop
      aesop
    aesop
  use qr
  constructor
  assumption
  have h_p_qr : isIndependentProduct s p qr := by
    constructor
    sorry
    sorry
  assumption

end Associativity
