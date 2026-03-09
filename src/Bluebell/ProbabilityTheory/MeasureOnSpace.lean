import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Bluebell.Algebra.DiscreteCMRA

/-! ## Independent product of probability measures -/

open ProbabilityTheory MeasureTheory

alias MeasureTheory.MeasureSpace.σAlg := MeasureSpace.toMeasurableSpace
alias MeasureTheory.MeasureSpace.μ := MeasureSpace.volume

variable {Ω Ω' : Type*}
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

/--
  An induction principle with respect to the trivial σ-algebra
  to show that a property P u holds where u is a measurable set
  with respect to the trivial σ-algebra, it suffices to show that
  P ∅ and P Ω
-/
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

section GeneratorMembership

variable {Ω : Type*} (m₁ m₂ : MeasurableSpace Ω)

def MeasurableSpace.sumGenerator (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {S : Set Ω | ∃ F G, S = F ∩ G ∧ MeasurableSet[m₁] F ∧ MeasurableSet[m₂] G}

variable
  {u v w : Set Ω}

/-- Every set in the generating set `w` is of the form `u ∩ v` -/
lemma exists_inter_measurableSet_of_mem_sumGenerator
  (hw : w ∈ MeasurableSpace.sumGenerator m₁ m₂)
  : ∃ u v, w = u ∩ v ∧ MeasurableSet[m₁] u ∧ MeasurableSet[m₂] v := by
  rcases hw with ⟨u, v, rfl, hu, hv⟩
  grind

@[aesop 50% apply]
lemma mem_sumGenerator_l (hu : MeasurableSet[m₁] u) :
  u ∈ MeasurableSpace.sumGenerator m₁ m₂ := by
  use u, ⊤
  aesop

@[aesop 50% apply]
lemma mem_sumGenerator_r (hu : MeasurableSet[m₂] u) :
  u ∈ MeasurableSpace.sumGenerator m₁ m₂ := by
  use ⊤, u
  aesop

lemma inter_mem_sumGenerator
  (hu : MeasurableSet[m₁] u) (hv : MeasurableSet[m₂] v) :
  u ∩ v ∈ MeasurableSpace.sumGenerator m₁ m₂ := by
  use u, v

theorem MeasurableSpace.generateFrom_sumGenerator_eq_sum :
  MeasurableSpace.generateFrom (MeasurableSpace.sumGenerator m₁ m₂)
    = MeasurableSpace.sum m₁ m₂ := by
  ext s
  refine ⟨?p, by apply MeasurableSpace.generateFrom_mono (fun _ _ ↦ by aesop)⟩
  let sumSp := MeasurableSet[m₁.sum m₂]
  apply MeasurableSpace.generateFrom_le
  rintro t ⟨u, ⟨v, _, _, _⟩⟩
  have h₂ : MeasurableSpace.sumGenerator m₁ m₂ ⊆ sumSp := fun w hw ↦ by
    obtain ⟨u, v, rfl, hu, hv⟩ :=
      @exists_inter_measurableSet_of_mem_sumGenerator Ω m₁ m₂ (w := w) hw
    unfold sumSp
    have h₁ : MeasurableSet[m₁.sum m₂] u := by
      have : u ∈ MeasurableSpace.sumGenerator m₁ m₂ := by aesop
      apply MeasurableSpace.measurableSet_generateFrom
      aesop
    have h₂ : MeasurableSet[m₁.sum m₂] v := by
      have : v ∈ MeasurableSpace.sumGenerator m₁ m₂ := by aesop
      apply MeasurableSpace.measurableSet_generateFrom
      aesop
    apply MeasurableSet.inter h₁ h₂
  aesop (add simp (show u ∩ v ∈ sumGenerator m₁ m₂ by use u, v))

end GeneratorMembership

section Sum

variable {Ω : Type*} (m m₁ m₂ : MeasurableSpace Ω)

@[simp]
def MeasurableSpace.sumUnit : MeasurableSpace Ω := ⊥

lemma MeasurableSpace.sum_identity
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

lemma MeasurableSpace.sum_comm
  : m₁.sum m₂ = m₂.sum m₁ := by
  let f : Set (Set Ω) := MeasurableSet[m₁]
  let g : Set (Set Ω) := MeasurableSet[m₂]
  unfold MeasurableSpace.sum
  have : f ∪ g = g ∪ f := by
    ext u
    grind
  grind

@[aesop 50% apply]
lemma mem_sum_l {u : Set Ω} (hu : MeasurableSet[m₁] u) :
  MeasurableSet[m₁.sum m₂] u := by
  simp
  let f : Set (Set Ω) := MeasurableSet[m₁]
  let g : Set (Set Ω) := MeasurableSet[m₁.sum m₂]
  have : f ⊆ g := by
    intro x hx
    apply MeasurableSpace.measurableSet_generateFrom
    aesop
  have : MeasurableSpace.generateFrom f = m₁ := by
    apply @MeasurableSpace.generateFrom_measurableSet Ω m₁
  aesop

@[aesop 50% apply]
lemma mem_sum_r {u : Set Ω} (hu : MeasurableSet[m₂] u) :
  MeasurableSet[m₁.sum m₂] u := by
  rw [MeasurableSpace.sum_comm]
  apply mem_sum_l
  exact hu

lemma mem_sum_inter {u v : Set Ω}
  (hu : MeasurableSet[m₁] u) (hv : MeasurableSet[m₂] v)
  : MeasurableSet[m₁.sum m₂] (u ∩ v) := by
  have : MeasurableSet[m₁.sum m₂] u := by aesop
  have : MeasurableSet[m₁.sum m₂] v := by aesop
  aesop

lemma subset_sum_l : m₁ ≤ m₁.sum m₂ := by
  intro t ht
  apply mem_sum_l
  exact ht

lemma subset_sum_r : m₂ ≤ m₁.sum m₂ := by
  intro t ht
  apply mem_sum_r
  exact ht

lemma MeasurableSpace.sum_assoc_left {m₁ m₂ m₃ : MeasurableSpace Ω}
  : (m₁.sum m₂).sum m₃ ≤ m₁.sum (m₂.sum m₃) := by
  have : m₁.sum m₂ ≤ m₁.sum (m₂.sum m₃) := by
    apply MeasurableSpace.generateFrom_le
    intro t ht
    rcases ht with h₁ | h₂
    aesop
    aesop
  have : m₃ ≤ m₁.sum (m₂.sum m₃) := by
    have : m₃ ≤ m₂.sum m₃ := by apply subset_sum_r
    have : m₂.sum m₃ ≤ m₁.sum (m₂.sum m₃) := by apply subset_sum_r
    grind
  apply MeasurableSpace.generateFrom_le
  intro t ht
  rcases ht with h₁ | h₂
  aesop
  aesop

lemma MeasurableSpace.sum_assoc_right {m₁ m₂ m₃ : MeasurableSpace Ω}
  : (m₁.sum m₂).sum m₃ ≥ m₁.sum (m₂.sum m₃) := by
  have : m₁ ≤ (m₁.sum m₂).sum m₃ := by
    have : m₁ ≤ m₁.sum m₂ := by apply subset_sum_l
    have : m₁.sum m₂ ≤ (m₁.sum m₂).sum m₃ := by apply subset_sum_l
    grind
  have : m₂.sum m₃ ≤ (m₁.sum m₂).sum m₃ := by
    have : m₂ ≤ (m₁.sum m₂).sum m₃ := by
      have : m₂ ≤ m₁.sum m₂ := by apply subset_sum_r
      have : m₁.sum m₂ ≤ (m₁.sum m₂).sum m₃ := by apply subset_sum_l
      grind
    have : m₃ ≤ (m₁.sum m₂).sum m₃ := by apply subset_sum_r
    apply MeasurableSpace.generateFrom_le
    intro t ht
    rcases ht with h₁ | h₂
    aesop
    aesop
  apply MeasurableSpace.generateFrom_le
  intro t ht
  rcases ht with h₁ | h₂
  aesop
  aesop

lemma MeasurableSpace.sum_assoc {m₁ m₂ m₃ : MeasurableSpace Ω}
  : (m₁.sum m₂).sum m₃ = m₁.sum (m₂.sum m₃) := by
  have : (m₁.sum m₂).sum m₃ ≤ m₁.sum (m₂.sum m₃) := by
    apply MeasurableSpace.sum_assoc_left
  have : (m₁.sum m₂).sum m₃ ≥ m₁.sum (m₂.sum m₃) := by
    apply MeasurableSpace.sum_assoc_right
  aesop

lemma MeasurableSpace.sum_mono {m₁ m₂ : MeasurableSpace Ω}
  : m₁ ≤ m₂.sum m₁ := by
  simp
  intro u hu
  have : MeasurableSet[m₂.sum m₁] u := by
    unfold MeasurableSpace.sum
    apply MeasurableSpace.measurableSet_generateFrom
    simp_all only [Set.mem_union]
    apply Or.inr
    exact hu
  simp_all only [sum]

lemma MeasurableSpace.sum_functorial {m m₁ m₂ : MeasurableSpace Ω}
  (h : m₁ ≤ m₂)
  : m₁.sum m ≤ m₂.sum m := by
  apply MeasurableSpace.generateFrom_le
  intro u hu
  rcases hu with h₁ | h₂
  · aesop
  · aesop

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

lemma mem_generator_imp_mem_sum (h : u ∈ generator p q)
  : MeasurableSet[p.ms.sum q.ms] u := by
  have h₁ := @MeasureOnSpace.generateFrom_generator_eq_sum Ω p q
  rw [← h₁]
  apply MeasurableSpace.measurableSet_generateFrom h
end

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

open MeasurableSpace in
lemma Measure.le_preserves_measure {p q : MeasurableSpace Ω}
  {h : p ≤ q} {μ : Measure[q] Ω}
  {u : Set Ω}
  {hu : MeasurableSet[p] u}
  : μ.cast p u = μ u := by
  have hu' : MeasurableSet[q] u := by apply h; exact hu
  unfold Measure.cast Measure.map!
  rw [Measure.map_apply] <;> aesop

lemma MeasureOnSpace.le_preserves_measure
  {p q : MeasureOnSpace Ω} (h : p ≤ q) {u} (hp : MeasurableSet[p.ms] u) : p.μ u = q.μ u := by
  rcases h with ⟨h₁, h₂⟩
  aesop (add simp Measure.le_preserves_measure)

instance [Inhabited Ω] : One (MeasureOnSpace Ω) where
  one := {ms := ⊥, μ := @Measure.dirac Ω ⊥ default}

instance [Inhabited Ω] : PartialOrder (MeasureOnSpace Ω) where
  le_antisymm m₁ m₂ h₁ h₂ := by
    have h : m₁.ms = m₂.ms := by
      ext u
      constructor
      have := h₁.1 u; aesop
      have := h₂.1 u; aesop
    ext u; aesop
    apply MeasureOnSpace.le_preserves_measure
    aesop; aesop

instance (Ω : Type*) [Inhabited Ω] : PartialOrder (PSpace Ω) where
  le_antisymm := by
    rintro ⟨m₁, p₁⟩ ⟨m₂, p₂⟩ h₁ h₂
    have : m₁ ≤ m₂ := by aesop
    have : m₂ ≤ m₁ := by aesop
    have : m₁ = m₂ := @le_antisymm (MeasureOnSpace Ω) _ m₁ m₂ (by aesop) (by aesop)
    aesop

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
  · exact @MeasureOnSpace.isPiSystem_generator Ω p.1 q.1
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
  simp
  unfold Measure.trim
  aesop

lemma Measure.trim_preserves_prob
  (f g : MeasurableSpace Ω)
  {μ : Measure[g] Ω}
  (hf : f ≤ g) (hp : IsProbabilityMeasure μ)
  : IsProbabilityMeasure (μ.trim hf) := by
  constructor
  unfold Measure.trim
  aesop

@[simp]
def PSpace.trim
  {p : PSpace Ω} {f : MeasurableSpace Ω} {h : f ≤ p.1.ms}
  : PSpace Ω := ⟨p.1.trim h, by
  simp
  constructor
  have : (p.1.trim h).μ Set.univ = 1 := by
    have := @Measure.trim_preserves_prob Ω f p.1.ms p.1.μ h p.2
    aesop
  aesop
⟩

end Trim

section Identity

lemma dirac_is_prob [Inhabited Ω] : IsProbabilityMeasure (@Measure.dirac Ω ⊥ default) := by
  apply isProbabilityMeasure_iff.2
  simp

def PSpace.unit [Inhabited Ω] : PSpace Ω := ⟨{
  ms := ⊥
  μ := @Measure.dirac Ω ⊥ default
}, dirac_is_prob⟩

instance [Inhabited Ω] : One (PSpace Ω) where
  one := PSpace.unit

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
theorem independentProduct_assoc [Inhabited Ω] {pq p q s r : PSpace Ω}
  (h_pq : isIndependentProduct pq p q)
  (h_pq_r : isIndependentProduct s pq r)
  : ∃ qr, isIndependentProduct qr q r ∧ isIndependentProduct s p qr
  := by
  let qr_ms : MeasurableSpace Ω := MeasurableSpace.sum q.1.ms r.1.ms
  have h : qr_ms <= s.1.ms := by
    unfold qr_ms
    rw [h_pq_r.1, h_pq.1]
    have : q.1.ms.sum r.1.ms ≤ p.1.ms.sum (q.1.ms.sum r.1.ms) := by
      apply MeasurableSpace.sum_mono
    rw [MeasurableSpace.sum_assoc]
    aesop
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
      have h₈ : q.1.ms.sum r.1.ms ≤ s.1.ms := by
        rw [h_pq_r.1, h_pq.1, MeasurableSpace.sum_assoc]
        apply MeasurableSpace.sum_mono
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
    rw [h_pq_r.1, h_pq.1, h_qr.1]
    apply @MeasurableSpace.sum_assoc Ω p.1.ms q.1.ms r.1.ms
    have h :
      ∀ u (hu : MeasurableSet[p.1.ms] u)
        vw (hvw : MeasurableSet[q.1.ms.sum r.1.ms] vw),
      s.1.μ (u ∩ vw) = p.1.μ u * qr.1.μ vw
    := by
      intro u hu
      apply MeasurableSpace.induction_on_inter
      apply MeasureOnSpace.isPiSystem_generator (p := q.1) (q := r.1)
      aesop
      intro t ht
      obtain ⟨v, w, rfl, hv, hw⟩ := exists_inter_measurableSet_of_mem_generator ht
      have h : u ∩ (v ∩ w) = (u ∩ v) ∩ w := by grind
      rw [h, h_pq_r.2, h_pq.2, h_qr.2]
      grind
      aesop
      aesop
      aesop
      aesop
      have := @mem_sum_inter Ω p.1.ms q.1.ms u v hu hv
      have : p.1.ms.sum q.1.ms = pq.1.ms := by rw [h_pq.1]
      aesop
      exact hw
      {
        intro t ht h
        have : u ∩ tᶜ = u \ (u ∩ t) := by grind
        have : s.1.μ (u \ (u ∩ t)) = s.1.μ u - s.1.μ (u ∩ t) := by
          have : s.1.μ Set.univ = 1 := s.2.measure_univ
          apply @measure_diff Ω s.1.ms s.1.μ u (u ∩ t)
          grind
          have : MeasurableSet[s.1.ms] (u ∩ t) := by
            rw [h_pq_r.1, h_pq.1, MeasurableSpace.sum_assoc]
            apply mem_sum_inter
            exact hu
            exact ht
          aesop
          apply s.measure_ne_top
        have : s.1.μ u = p.1.μ u := by
          have : u = (u ∩ Set.univ) ∩ Set.univ := by grind
          have h₁ : s.1.μ u = s.1.μ ((u ∩ Set.univ) ∩ Set.univ) := by grind
          have h₂ : q.1.μ Set.univ = 1 := q.2.measure_univ
          have h₃ : r.1.μ Set.univ = 1 := r.2.measure_univ
          rw [h₁, h_pq_r.2, h_pq.2, h₂, h₃]
          simp
          exact hu
          apply MeasurableSet.univ
          have h₄ := @mem_sum_inter Ω p.1.ms q.1.ms u Set.univ hu MeasurableSet.univ
          rw [h_pq.1]
          exact h₄
          apply MeasurableSet.univ
        have : p.1.μ u - p.1.μ u * qr.1.μ t = p.1.μ u * (1 - qr.1.μ t) := by
          have := @ENNReal.mul_sub (p.1.μ u) 1 (qr.1.μ t)
          aesop
        have h₃ : qr.1.μ tᶜ = 1 - qr.1.μ t := by
          have h := @measure_compl Ω qr.1.ms (μ := qr.1.μ) (s := t) ht
          have : qr.1.μ t ≠ ⊤ := qr.measure_ne_top
          have := qr.2.measure_univ
          aesop
        calc
              s.1.μ (u ∩ tᶜ)
          _ = s.1.μ (u \ (u ∩ t)) := by aesop
          _ = s.1.μ u - s.1.μ (u ∩ t) := by aesop
          _ = s.1.μ u - p.1.μ u * qr.1.μ t := by aesop
          _ = p.1.μ u - p.1.μ u * qr.1.μ t := by aesop
          _ = p.1.μ u * (1 - qr.1.μ t) := by aesop
          _ = p.1.μ u * qr.1.μ tᶜ := by aesop
      }
      {
        intro us hdis hus ih
        have : u ∩ ⋃ i, us i = ⋃ i, u ∩ us i := by aesop
        have : s.1.μ (⋃ i, u ∩ us i) = ∑' i, s.1.μ (u ∩ us i) := by
          have hus' : ∀ i, MeasurableSet[s.1.ms] (u ∩ us i) := by
            intro i
            have hus_i := hus i
            rw [h_pq_r.1, h_pq.1, MeasurableSpace.sum_assoc]
            apply mem_sum_inter
            exact hu
            exact hus_i
          have h : Pairwise (Function.onFun Disjoint (fun k ↦ u ∩ us k)) := by
            intro k l p
            have h₁ := hdis p
            have h₂ : Disjoint (us k) (us l) := by apply h₁
            have h₃ := @Disjoint.inter_left' Ω (us k) (us l) u h₂
            have := @Disjoint.inter_right' Ω (u ∩ us k) (us l) u h₃
            aesop
          have := @s.1.μ.m_iUnion (fun i ↦ u ∩ us i) hus' h
          aesop
        have : ∑' i, s.1.μ (u ∩ us i) = ∑' i, p.1.μ u * qr.1.μ (us i) := by
          have : ∀ i, s.1.μ (u ∩ us i) = p.1.μ u * qr.1.μ (us i) := by
            intro i
            have := ih i
            aesop
          aesop
        have : ∑' i, p.1.μ u * qr.1.μ (us i) = p.1.μ u *  ∑' i, qr.1.μ (us i) := by
          apply ENNReal.tsum_mul_left
        have : p.1.μ u *  ∑' i, qr.1.μ (us i) = p.1.μ u * qr.1.μ (⋃ i, us i) := by
          congr
          have := @qr.1.μ.m_iUnion us hus hdis
          aesop
        calc
              s.1.μ (u ∩ ⋃ i, us i)
          _ = s.1.μ (⋃ i, u ∩ us i) := by aesop
          _ = ∑' i, s.1.μ (u ∩ us i) := by aesop
          _ = ∑' i, p.1.μ u * qr.1.μ (us i) := by aesop
          _ = p.1.μ u *  ∑' i, qr.1.μ (us i) := by aesop
          _ = p.1.μ u * qr.1.μ (⋃ i, us i) := by aesop
      }
      have := @MeasurableSpace.generateFrom_sumGenerator_eq_sum Ω q.1.ms r.1.ms
      grind
    aesop
  assumption

theorem independentProduct_assoc_right [Inhabited Ω] {p q r qr s : PSpace Ω}
  (h_qr : isIndependentProduct qr q r)
  (h_p_qr : isIndependentProduct s p qr)
  : ∃ pq, isIndependentProduct pq p q ∧ isIndependentProduct s pq r := by
  have h₁ : qr.isIndependentProduct r q := by
    apply @independentProduct_comm Ω _ qr q r h_qr
  have h₂ : s.isIndependentProduct qr p := by
    apply @independentProduct_comm Ω _ s p qr h_p_qr
  have h₃ := @independentProduct_assoc Ω _ qr r q s p h₁ h₂
  obtain ⟨qp, h₃⟩ := h₃
  have h₄ : qp.isIndependentProduct p q := by
    have : qp.isIndependentProduct p q := by
      have := @independentProduct_comm Ω _ qp q p
      aesop
    have : s.isIndependentProduct r qp := by
      have := h₃.2
      aesop
    aesop
  have h₅ : s.isIndependentProduct qp r := by
    have := @independentProduct_comm Ω _
    aesop
  aesop

end Associativity

section PSp

variable {Ω : Type*}

@[simp, grind]
def PSpace.incompatible (p q : PSpace Ω) :=
  ¬∃r : PSpace Ω, r.isIndependentProduct p q

theorem PSpace.incompatible_symm [Inhabited Ω] {p q : PSpace Ω}
  (h : p.incompatible q) : q.incompatible p := by
  simp_all
  intro x hx
  have : x.isIndependentProduct p q := by apply independentProduct_comm hx
  have := h x (by aesop)
  contradiction

theorem PSpace.incompatible_mono_left {p q r qr : PSpace Ω}
  (hinc : p.incompatible q) (hqr : qr.isIndependentProduct q r)
  : p.incompatible qr := by
  simp_all
  intro x hx
  have : ∃ y : PSpace Ω, y.isIndependentProduct p q := by
    let pqms := p.1.ms.sum q.1.ms
    have hmsle : pqms ≤ x.1.ms := by
      unfold pqms
      have := @MeasurableSpace.sum_comm Ω
      have h₁ := @MeasurableSpace.sum_mono Ω
      rw [hx.1, hqr.1]
      have h₂ : p.1.ms.sum (q.1.ms.sum r.1.ms) = (p.1.ms.sum q.1.ms).sum (r.1.ms) := by
        have := @MeasurableSpace.sum_assoc Ω
        aesop
      rw [h₂]
      grind
    let x' := @x.trim Ω pqms (by aesop)
    have : x'.isIndependentProduct p q := by
      unfold PSpace.isIndependentProduct
      constructor
      aesop
      intro u hu v hv
      have : x'.1.μ ((u ∩ v) ∩ Set.univ) = p.1.μ u * qr.1.μ (v ∩ Set.univ) := by
        have h₁ : v ∩ Set.univ = v := by grind
        have h₂ : (u ∩ v) ∩ Set.univ = u ∩ (v ∩ Set.univ) := by grind
        rw [h₂, h₁]
        have : MeasurableSet[pqms] (u ∩ v) := by
          unfold pqms
          have : MeasurableSet[pqms] u := by apply @mem_sum_l Ω p.1.ms q.1.ms u hu
          have : MeasurableSet[pqms] v := by apply @mem_sum_r Ω p.1.ms q.1.ms v hv
          have := @MeasurableSet.inter Ω pqms u v (by aesop) (by aesop)
          assumption
        have h₃ := @x.1.trim_eq Ω pqms (by aesop) (u ∩ v) (by aesop)
        have : x.1.μ (u ∩ v) = p.1.μ u * qr.1.μ v := by
          rw [hx.2]
          aesop
          have := @mem_sum_l Ω q.1.ms r.1.ms v hv
          rw [hqr.1]
          assumption
        have : x'.1.μ (u ∩ v) = x.1.μ (u ∩ v) := by aesop
        grind
      have : p.1.μ u * qr.1.μ (v ∩ Set.univ) = p.1.μ u * (q.1.μ v * r.1.μ Set.univ) := by
        rw [hqr.2]
        exact hv
        aesop
      calc
          x'.1.μ (u ∩ v)
      _ = x'.1.μ ((u ∩ v) ∩ Set.univ) := by aesop
      _ = p.1.μ u * qr.1.μ (v ∩ Set.univ) := by aesop
      _ = p.1.μ u * (q.1.μ v * r.1.μ Set.univ) := by aesop
      _ = p.1.μ u * (q.1.μ v * 1) := by have := r.2.measure_univ; aesop
      _ = p.1.μ u * q.1.μ v := by aesop
    aesop
  aesop

lemma PSpace.measure_compl {p : PSpace Ω} {u : Set Ω}
  (h : MeasurableSet[p.1.ms] u)
  : p.1.μ uᶜ = 1 - p.1.μ u := by
  have : p.1.μ Set.univ = 1 := p.2.measure_univ
  rw [← this]
  apply MeasureTheory.measure_compl
  exact h
  aesop

theorem PSpace.functoriality [Inhabited Ω] {p q a pa qa : PSpace Ω}
  (hpa : pa.isIndependentProduct p a)
  (hqa : qa.isIndependentProduct q a)
  (hlt : p ≤ q)
  : pa ≤ qa := by
  have hms : pa.1.ms ≤ qa.1.ms := by
    have := @MeasurableSpace.sum_functorial Ω a.1.ms p.1.ms q.1.ms hlt.1
    have := hpa.1
    have := hqa.1
    aesop
  constructor; aesop
  have := hlt.2
  have : ∀ {u : Set Ω}, MeasurableSet[pa.1.ms] u → pa.1.μ u = qa.1.μ u := by
    apply MeasurableSpace.induction_on_inter
    · exact @MeasureOnSpace.isPiSystem_generator Ω p.1 a.1
    · aesop
    · intro t ht
      obtain ⟨u, v, h, hu, hv⟩ :=
        @exists_inter_measurableSet_of_mem_sumGenerator Ω p.1.ms a.1.ms t ht
      rw [h, hpa.2, hqa.2]
      have : p.1.μ u = q.1.μ u := by
        have : p.1.μ = q.1.μ.cast p.1.ms := hlt.2
        rw [this]
        apply Measure.le_preserves_measure
        exact hlt.1
        exact hu
      aesop
      exact hlt.1 u hu; exact hv; exact hu; exact hv
    · intro t ht h
      calc
            pa.1.μ tᶜ
        _ = 1 - pa.1.μ t := by
          have := @PSpace.measure_compl Ω pa t (by
            have := @MeasurableSet.compl Ω t pa.1.ms ht; aesop)
          aesop
        _ = 1 - qa.1.μ t := by aesop
        _ = qa.1.μ tᶜ := by
          have := @PSpace.measure_compl Ω qa t
          have := hms t ht
          aesop
    · intro us hdis hus heq
      calc
            pa.1.μ (⋃ i, us i)
        _ = ∑' i, pa.1.μ (us i) := measure_iUnion hdis hus
        _ = ∑' i, qa.1.μ (us i) := by aesop
        _ = qa.1.μ (⋃ i, us i) := Eq.symm (measure_iUnion hdis fun i => hms (us i) (hus i))
    · have := @MeasurableSpace.generateFrom_sumGenerator_eq_sum Ω p.1.ms a.1.ms
      have : p.1.ms.sumGenerator a.1.ms = generator p.1 a.1 := by rfl
      rw [hpa.1]
      aesop
  apply @Measure.ext Ω pa.1.ms
  intro u hu
  have := @Measure.le_preserves_measure Ω pa.1.ms qa.1.ms hms qa.1.μ u hu
  aesop

lemma PSpace.incompatible_mono_right [Inhabited Ω] {p q r pq : PSpace Ω}
  (hinc : q.incompatible r) (hpq : pq.isIndependentProduct p q)
  : pq.incompatible r := by
  have : r.incompatible q := by apply PSpace.incompatible_symm (by aesop)
  have : pq.isIndependentProduct q p := by apply independentProduct_comm (by aesop)
  have := @PSpace.incompatible_mono_left Ω r q (by aesop) pq (by aesop) (by aesop)
  have : pq.incompatible r := by
    apply PSpace.incompatible_symm (by aesop)
  assumption

@[simp, grind]
def PSp.mul [Inhabited Ω] (p q : PSp Ω) : PSp Ω :=
  match p, q with
  | none, _ => none
  | _, none => none
  | some p, some q => by
    by_cases h : ∃ s, PSpace.isIndependentProduct s p q
    exact (some h.choose)
    exact none

@[simp]
def PSp.unit [Inhabited Ω] : PSp Ω :=
  some PSpace.unit

instance [Inhabited Ω] : Valid (PSp Ω) where
  valid x := x ≠ ⊤

instance [Inhabited Ω] : One (PSp Ω) where
  one := PSp.unit

instance [Inhabited Ω] : Mul (PSp Ω) where
  mul := PSp.mul

instance [Inhabited Ω] : HMul (PSp Ω) (PSp Ω) (PSp Ω) where
  hMul := PSp.mul

/-- an inversion lemma extracting the property of independent products in mul -/
lemma mul_inversion [Inhabited Ω] {x y xy : PSpace Ω}
  (h : PSp.mul (some x) (some y) = some xy)
  : xy.isIndependentProduct x y := by
  simp_all
  by_cases h₁ : ∃ s : PSpace Ω, s.isIndependentProduct x y
  simp_all
  have : h₁.choose = xy := by grind
  grind
  simp_all

lemma mul_respect_independentProduct [Inhabited Ω] {x y xy : PSpace Ω}
  (h : xy.isIndependentProduct x y) : PSp.mul (some x) (some y) = some xy := by
  cases h₁ : PSp.mul (some x) (some y) with
  | none =>
    have := @mul_inversion Ω _ x y xy
    aesop
  | some xy' =>
    have : xy'.isIndependentProduct x y := by
      apply mul_inversion
      exact h₁
    have := @PSpace.uniqueness Ω xy xy' x y h (by aesop)
    aesop

theorem PSp.mul_idem [Inhabited Ω] {p : PSp Ω} : PSp.unit.mul p = p := by
  cases h : p with
  | none => aesop
  | some x =>
    simp_all
    by_cases h : ∃ s : PSpace Ω, s.isIndependentProduct PSpace.unit x
    · have := @indepenendentProduct_identity Ω _
      have h₁ : h.choose = x :=
        @PSpace.uniqueness Ω h.choose x (PSpace.unit) x h.choose_spec (by aesop)
      aesop
    · have h₃ : (∃ s : PSpace Ω, s.isIndependentProduct PSpace.unit x) := by
        use x
        have := @indepenendentProduct_identity Ω _
        aesop
      contradiction

theorem PSp.mul_comm [Inhabited Ω] {p q : PSp Ω} : p.mul q = q.mul p :=
  match p, q with
  | none, _ => by grind
  | _, none => by grind
  | some x, some y => by
    simp
    by_cases h : ∃ s : PSpace Ω, s.isIndependentProduct x y
    · have h₁ : h.choose.isIndependentProduct y x := by
        apply independentProduct_comm; grind
      have h₂ : ∃ s' : PSpace Ω, s'.isIndependentProduct y x := by use h.choose
      simp_all
      congr
      ext z
      constructor
      apply independentProduct_comm
      apply independentProduct_comm
    · simp_all
      intro a
      have : ¬a.isIndependentProduct x y := by
        intro h₁
        have := h a
        contradiction
      intro h₂
      have : a.isIndependentProduct x y := by
        apply independentProduct_comm
        aesop
      contradiction

lemma exists_of_ne_none {α} {a : Option α} (h : a ≠ none) :
  ∃ b, a = some b := by
  cases a with
  | none => contradiction
  | some b => exact ⟨b, rfl⟩

lemma PSp.inversion [Inhabited Ω] {p : PSp Ω}
  (h : p ≠ ⊤)
  : ∃ x, p = some x := by
  cases p with
  | none => contradiction
  | some x => use x

theorem PSp.mul_assoc [Inhabited Ω] {p q r : PSp Ω}
  : (p.mul q).mul r = p.mul (q.mul r) := by
  cases h₁ : p with
  | none => aesop | some x => cases h₂ : q with
  | none => aesop | some y => cases h₃ : r with
  | none => aesop | some z =>
  cases h₄ : mul (some x) (some y) with
  | none =>
    simp_all
    by_cases h' : ∃ s : PSpace Ω, s.isIndependentProduct y z
    simp_all
    intro a ha
    have h₆ : x.incompatible y := by simp_all
    have := @PSpace.incompatible_mono_left Ω x y z h'.choose h₆ h'.choose_spec
    grind
    simp_all
  | some xy =>
  cases h₅ : mul (some y) (some z) with
  | none =>
    simp_all
    by_cases h₆ : ∃ s : PSpace Ω, s.isIndependentProduct x y
    have h₇ : y.incompatible z := by simp_all
    have := @PSpace.incompatible_mono_right Ω _ x y z h₆.choose h₇ h₆.choose_spec
    grind
    simp_all
  | some yz =>
    have h₈ : xy.isIndependentProduct x y := by
      apply @mul_inversion Ω _ x y xy h₄
    cases h₉ : mul (some xy) (some z) with
    | none =>
      by_contra h
      have hcon : ∃ x_yz : PSpace Ω, mul (some x) (some yz) = some x_yz := by
        have := @PSp.inversion Ω _ (mul (some x) (some yz)) (by aesop)
        grind
      obtain ⟨x_yz, hcon⟩ := hcon
      have : x_yz.isIndependentProduct x yz := by
        apply mul_inversion
        grind
      have : x_yz.isIndependentProduct xy z := by
        have : yz.isIndependentProduct y z := by
          apply mul_inversion
          assumption
        have hgoal := @independentProduct_assoc_right Ω _ x y z yz x_yz (by aesop) (by aesop)
        have : hgoal.choose = xy := by
          have hxy : xy.isIndependentProduct x y := by
            apply mul_inversion
            assumption
          have := @PSpace.uniqueness Ω hgoal.choose xy x y (by grind) hxy
          assumption
        grind
      have : mul (some xy) (some z) = some x_yz := by
        apply mul_respect_independentProduct
        grind
      have : some x_yz = none := by aesop
      grind
    | some xy_z =>
      have h₁₀ : xy_z.isIndependentProduct xy z := by
        apply mul_inversion
        assumption
      have h_goal := @independentProduct_assoc Ω _ xy x y xy_z z h₈ h₁₀
      have h' : h_goal.choose = yz := by
        have h₁ : h_goal.choose.isIndependentProduct y z := by grind
        have h_yz : yz.isIndependentProduct y z := by
          apply mul_inversion
          assumption
        have := @PSpace.uniqueness Ω h_goal.choose yz y z h₁ h_yz
        assumption
      have := mul_respect_independentProduct (x := x) (y := yz) (xy := xy_z)
      grind

theorem PSp.mul_defined_imp_defined
  [Inhabited Ω] {p q : PSp Ω} (h : p.mul q ≠ ⊤)
  : p ≠ ⊤ :=
  match p, q with
  | none, _ => by aesop
  | _, none => by intro h₁; simp_all; contradiction
  | some x, some y => by aesop

end PSp

instance [Inhabited Ω] : CommMonoid (PSp Ω) := {
  mul_assoc p q r := by apply PSp.mul_assoc
  mul_comm p q := by apply PSp.mul_comm
  one_mul a := PSp.mul_idem
  mul_one a := by
    calc
      a * 1
    _ = 1 * a := by apply PSp.mul_comm
    _ = a := by apply PSp.mul_idem
}

instance [Inhabited Ω] : PartialOrder (PSp Ω) := {
  le_antisymm := by
    intro p₁ p₂ h₁ h₂
    cases p₁ with
    | none => cases p₂ with
      | none => aesop
      | some q₂ => contradiction
    | some q₁ => cases p₂ with
      | none => contradiction
      | some q₂ =>
        have : q₁ ≤ q₂ := by grind
        have : q₂ ≤ q₁ := by grind
        have : q₁ = q₂ := by
          have := @le_antisymm (PSpace Ω) _ q₁ q₂
          aesop
        aesop
}

lemma PSp.ge_top_imp_top {p : PSp Ω} (h : ⊤ ≤ p) : p = ⊤ := by
  cases p; rfl; contradiction

lemma PSp.le_top' {p : PSp Ω} : p ≤ ⊤ := by
  apply le_top

instance [Inhabited Ω] : OrderedUnitalResourceAlgebra (PSp Ω) := {
  valid_one := by
    unfold valid
    have : (1 : PSp Ω) ≠ ⊤ := by aesop
    assumption
  elim := by
    intro a x y ha
    unfold Function.swap
    cases a; simp;
    have h : PSp.mul x none = PSp.mul y none := by aesop
    simp [HMul.hMul, Mul.mul]
    aesop
    simp [HMul.hMul, Mul.mul]
    cases x; simp
    cases y; simp
    · rename_i x
      have : some x = none := by
        have := @PSp.ge_top_imp_top Ω (some x) ha
        aesop
      contradiction
    cases y
    simp
    rename_i y x
    by_cases h : ∃ s : PSpace Ω, s.isIndependentProduct x y
    · simp [h]
      apply PSp.le_top'
    · simp [h]
    rename_i a x y
    simp_all
    have hxy : x ≤ y := by
      apply WithTop.coe_le_coe.1
      exact ha
    by_cases h₁ : ∃ t : PSpace Ω, t.isIndependentProduct y a
    by_cases h₂ : ∃ s : PSpace Ω, s.isIndependentProduct x a
    · simp [h₁, h₂]
      have h := @PSpace.functoriality Ω _ x y a h₂.choose h₁.choose h₂.choose_spec h₁.choose_spec hxy
      apply WithTop.coe_le_coe.2
      exact h
    · simp [h₁, h₂]
      have : ∃ xa : PSpace Ω, xa.isIndependentProduct x a := by
        obtain ⟨ya, h₁⟩ := h₁
        let xams := x.1.ms.sum a.1.ms
        have hxams : xams ≤ ya.1.ms := by
          have : ya.1.ms = y.1.ms.sum a.1.ms := h₁.1
          have := @MeasurableSpace.sum_functorial Ω a.1.ms x.1.ms y.1.ms hxy.1
          aesop
        let xa := @ya.trim Ω xams (by assumption)
        use xa
        constructor
        · rfl
        · intro u hu v hv
          have hu' : MeasurableSet[y.1.ms] u := hxy.1 u hu
          have huv : MeasurableSet[xams] (u ∩ v) := by
            apply MeasurableSet.inter; aesop; aesop
          have : xa.1.μ (u ∩ v) = ya.1.μ (u ∩ v) := by
            have := @ya.1.trim_eq Ω xams (by aesop) (u ∩ v) (by aesop)
            aesop
          calc
                xa.1.μ (u ∩ v)
            _ = ya.1.μ (u ∩ v) := by aesop
            _ = y.1.μ u * a.1.μ v := h₁.2 u hu' v hv
            _ = x.1.μ u * a.1.μ v := by
              have := @MeasureOnSpace.le_preserves_measure Ω x.1 y.1 hxy u hu
              aesop
      contradiction
    · simp [h₁]
      by_cases h₂ : ∃ s : PSpace Ω, s.isIndependentProduct x a
      · simp [h₂, LE.le]
        apply PSp.le_top'
      · simp [h₂]
  valid_mono := by
    intro ps₁ ps₂ h₁ h₂
    cases ps₁ with
    | none =>
      have : ps₂ = ⊤ := @PSp.ge_top_imp_top Ω ps₂ h₁
      aesop
    | some p₁ => cases ps₂ with
      | none => contradiction
      | some p₂ => intro h; contradiction
  valid_mul := by apply PSp.mul_defined_imp_defined
}

section PSpPm

/-- 𝕏 in the paper -/
abbrev Var : Type := Nat

/-- 𝕍 in the paper -/
abbrev Val : Type := Int

/-- 𝕊 in the paper -/
abbrev State : Type := Var → Val

def equivProd {α V : Type*} (p : Permission α) :
  (α → V) ≃ ({ a // p a > 0 } → V) × ({ a // p a = 0 } → V) :=
  {
    toFun f := ⟨(f ·), (f ·)⟩,
    invFun f x := if h : p x > 0 then f.1 ⟨x, h⟩ else f.2 ⟨x, by simpa using h⟩,
    left_inv := by simp [Function.LeftInverse]
    right_inv := by
      simp only [Function.RightInverse, Function.LeftInverse, gt_iff_lt, Subtype.coe_eta,
        Prod.forall, Prod.mk.injEq]
      intros f₁ f₂
      constructor <;> ext x <;> simp [x.2]
  }

@[simp]
def MeasureOnSpace.map (h : Ω → Ω') (ms : MeasureOnSpace Ω) : MeasureOnSpace Ω' :=
  letI := ms.ms.map h
  ⟨this, @Measure.map _ _ ms.ms _ h ms.μ⟩

@[simp]
def PSpace.map (f : Ω → Ω') (ps : PSpace Ω) : PSpace Ω' := ⟨ps.1.map f, by
  refine isProbabilityMeasure_iff.mpr ?_
  have := @Measure.map_apply Ω Ω' ps.1.ms (ps.1.ms.map f) ps.1.μ f (fun ⦃t⦄ a => a) Set.univ (by simp)
  have : ps.1.μ (f ⁻¹' Set.univ) = 1 := by
    have : f ⁻¹' Set.univ = Set.univ := by simp
    have := ps.2.measure_univ
    aesop
  aesop
⟩

theorem PSpace.map_preserves_independentProduct
  {p q pq : PSpace Ω} {f : Ω ≃ Ω'}
  (hind : pq.isIndependentProduct p q)
  : (pq.map f).isIndependentProduct (p.map f) (q.map f) :=
  sorry

@[simp]
def MeasureOnSpace.tensor (m : MeasureOnSpace Ω) (n : MeasureOnSpace Ω') : MeasureOnSpace (Ω × Ω') := {
  ms := m.ms.prod n.ms
  μ := @Measure.prod Ω Ω' m.ms n.ms m.μ n.μ
}
variable {Ω : Type}

@[simp]
def PSpace.tensor (P : PSpace Ω) (Q : PSpace Ω') : PSpace (Ω × Ω') := {
  val := P.1.tensor Q.1,
  property := by
    refine isProbabilityMeasure_iff.mpr ?_
    have := P.2
    have := Q.2
    have := @Measure.prod_prod Ω Ω' P.1.ms Q.1.ms P.1.μ Q.1.μ _ Set.univ Set.univ
    aesop
}

lemma MeasureOnSpace.map_measurable
  {Ω Ω' : Type u}
  {m : MeasureOnSpace Ω} {f : Ω ≃ Ω'} {u : Set Ω}
  : MeasurableSet[m.ms] u ↔ MeasurableSet[m.ms.map f] (f '' u) := by
  constructor
  · intro hu
    let u' := f '' u
    have := @MeasurableSpace.map_def Ω Ω' m.ms f u'
    aesop
  · intro hu
    let u' := f '' u
    have := @MeasurableSpace.map_def Ω Ω' m.ms f u'
    aesop

lemma MeasureOnSpace.map_measurable_inv
  {Ω Ω' : Type u}
  {m : MeasureOnSpace Ω} {f : Ω ≃ Ω'} {u : Set Ω'}
  : MeasurableSet[m.ms] (f ⁻¹' u) ↔ MeasurableSet[m.ms.map f] u := by
  aesop

def PSpace.compatiblePerm (P : PSpace (Var → Val)) (p : Permission Var) : Prop :=
  ∃ (P' : PSpace ({a : Var // p a > 0} → Val)),
    P'.tensor 1 = P.map (equivProd p)

@[simp]
def PSp.compatiblePerm
  (P : PSp State) (p : Permission Var) : Prop :=
  match P with
  | some P' => PSpace.compatiblePerm P' p
  | none => True

instance : Inhabited State where
  default := fun _ ↦ 0

def PSpRA : OrderedUnitalResourceAlgebra (PSp State) :=
  inferInstance

def PermissionRA : OrderedUnitalResourceAlgebra (Permission Var) :=
  inferInstance

def ProductRA : OrderedUnitalResourceAlgebra (PSp State × Permission Var) :=
  PSpRA.product PermissionRA

@[simp]
def Compatible (x : PSp State × Permission Var) : Prop :=
  x.1.compatiblePerm x.2

@[simp]
def PermissionOk (p : Permission α) :=
  {a : α // p a > 0} -> Val

@[simp]
def PermissionFail (p : Permission α) :=
  {a : α // p a = 0} -> Val

instance {p : Permission α} : Inhabited (PermissionOk p) where
  default := fun _ ↦ 0

instance {p : Permission α} : Inhabited (PermissionFail p) where
  default := fun _ ↦ 0

@[simp]
def honeLHS : PSpace (@PermissionOk Var 1 × @PermissionFail Var 1) :=
  PSpace.tensor
    (unit : PSpace (PermissionOk 1))
    (1 : PSpace (PermissionFail 1))

@[simp]
def honeRHS : PSpace (@PermissionOk Var 1 × @PermissionFail Var 1) :=
  PSpace.map (equivProd 1) unit

example : (⊥ : MeasurableSpace α).prod (⊥ : MeasurableSpace β) = ⊥ := by
  simp [MeasurableSpace.prod]

lemma honeLHSms_eq_bot : honeLHS.1.ms = ⊥ := by
  let unitL : PSpace (@PermissionOk Var 1) := unit
  let unitR : PSpace (@PermissionFail Var 1) := unit
  let unitLR : PSpace (@PermissionOk Var 1 × @PermissionFail Var 1) := unit
  have : unitL.1.ms.prod unitR.1.ms = unitLR.1.ms := by
    have : unitL.1.ms = ⊥ := by aesop
    have : unitR.1.ms = ⊥ := by aesop
    have : unitLR.1.ms = ⊥ := by aesop
    simp [MeasurableSpace.prod]
    aesop
  aesop

lemma preimage_empty_or_univ_of_bijective
  {Ω Ω' : Type u}
  (f : Ω ≃ Ω') {u : Set Ω'} (h : f ⁻¹' u = ∅ ∨ f ⁻¹' u = Set.univ)
  :  u = ∅ ∨ u = Set.univ := by
  have : u = f '' (f ⁻¹' u) := by aesop
  rcases h with h₁ | h₂
  · rw [h₁] at this
    aesop
  · rw [h₂] at this
    aesop

lemma MeasurableSpace.map_bot_eq_bot {Ω Ω' : Type u} (f : Ω ≃ Ω')
  : MeasurableSpace.map f ⊥ = ⊥ := by
  ext u; constructor
  · intro hu
    have hbot := (@MeasurableSpace.map_def (f := f) Ω Ω' ⊥ u).1 hu
    have : f ⁻¹' u = ∅ ∨ f ⁻¹' u = Set.univ := measurableSet_bot_iff.mp hu
    have : u = ∅ ∨ u = Set.univ := by
      have := @preimage_empty_or_univ_of_bijective Ω Ω'
      aesop
    aesop
  · intro hu
    have := MeasurableSpace.measurableSet_bot_iff.mp hu
    aesop

lemma honeRHSms_eq_bot : honeRHS.1.ms = ⊥ := by
  ext u; constructor
  · intro hu
    refine MeasurableSpace.measurableSet_bot_iff.mpr ?_
    simp [PSpace.unit] at hu
    have h := @MeasurableSpace.map_bot_eq_bot
      (Var → Val) (@PermissionOk Var 1 × @PermissionFail Var 1)
      (@equivProd Var Val 1)
    simp [PermissionOk, PermissionFail] at h
    rw [h] at hu
    exact MeasurableSpace.measurableSet_bot_iff.mp hu
  · intro hu
    have : u = ∅ ∨ u = Set.univ := MeasurableSpace.measurableSet_bot_iff.mp hu
    aesop

lemma honeLHS_eq_honeRHS : honeLHS = honeRHS := by
  have honeLHSms_eq_honeRHSms : honeLHS.1.ms = honeRHS.1.ms := by
    have := honeLHSms_eq_bot
    have := honeRHSms_eq_bot
    aesop
  ext u
  · aesop
  · rename_i hu
    rw [honeLHSms_eq_bot] at hu
    have h : u = ∅ ∨ u = Set.univ := MeasurableSpace.measurableSet_bot_iff.mp hu
    rcases h with h₁ | h₂
    · aesop
    · have := honeLHS.2.measure_univ
      have := honeRHS.2.measure_univ
      aesop

lemma hone : Compatible ⟨1, 1⟩ := by
  let Ω₁ := PermissionOk (1 : Permission Var)
  let Ω₂ := PermissionFail (1 : Permission Var)
  simp
  split
  · rename_i p hunit
    unfold PSpace.compatiblePerm
    use unit;
    have : p = unit := by
      simp [OfNat.ofNat, One.one] at hunit
      grind
    have := honeLHS_eq_honeRHS
    aesop
  · simp

lemma PSpace.compatiblePerm_implies_independentProduct_compatiblePerm
  {P₁ P₂ P : PSpace (Var → Val)} {p₁ p₂ : Permission Var}
  (h₁ : P₁.compatiblePerm p₁) (h₂ : P₂.compatiblePerm p₂)
  (hind : P.isIndependentProduct P₁ P₂)
  : P.compatiblePerm (p₁ * p₂) := by
  let S₁ := {x : Var // p₁ x = 0}
  let S₁c := {x : Var // p₁ x > 0}
  let S₂ := {x : Var // p₂ x = 0}
  let S₂c := {x : Var // p₂ x > 0}
  have h₁ : ∃ P₁' : PSpace (S₁c → Val), P₁'.tensor 1 = P₁.map (equivProd p₁) := by aesop
  have h₂ : ∃ P₂' : PSpace (S₂c → Val), P₂'.tensor 1 = P₂.map (equivProd p₂) := by aesop
  obtain ⟨P₁', h₁⟩ := h₁
  obtain ⟨P₂', h₂⟩ := h₂
  have : (P.map (equivProd (p₁ * p₂))).isIndependentProduct
    (P₁.map (equivProd (p₁ * p₂)))
    (P₂.map (equivProd (p₁ * p₂))) := map_preserves_independentProduct hind
  sorry

lemma hprod (x y : PSp State × Permission Var)
  (h₁ : Compatible x) (h₂ : Compatible y)
  : Compatible (ProductRA.mul x y) := by
  obtain ⟨P₁, f₁⟩ := x
  obtain ⟨P₂, f₂⟩ := y
  cases hp₁ : P₁ with
  | none => trivial
  | some p₁ => cases hp₂ : P₂ with
  | none => trivial
  | some p₂ =>
    cases h : ProductRA.mul (some p₁, f₁) (some p₂, f₂) with
    | mk P₃ f₃ => cases hP : P₃ with
    | none => trivial
    | some p₃ =>
      simp [
        ProductRA, OrderedUnitalResourceAlgebra.product,
        Prod.instCommMonoid, Prod.instMonoid, Prod.instSemigroup, Prod.instMul
      ] at h
      have hind : p₃.isIndependentProduct p₁ p₂ := by
        refine mul_inversion ?_; aesop
      have : f₃ = f₁ * f₂ := by aesop
      simp_all only [Compatible, PSp.compatiblePerm]
      have : p₁.compatiblePerm f₁ := by assumption
      have : p₂.compatiblePerm f₂ := by assumption
      have := @PSpace.compatiblePerm_implies_independentProduct_compatiblePerm
      aesop

def PSpPm :=
  ProductRA.subalgebra
    (p := fun (P, p) ↦ PSp.compatiblePerm P p)
    hone hprod

end PSpPm
