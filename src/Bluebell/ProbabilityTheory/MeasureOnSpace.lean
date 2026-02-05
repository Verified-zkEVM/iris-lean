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

/- We define `(𝓕, μ) ≤ (𝓖, ν)` if `𝓕 ⊆ 𝓖` and `μ` is the restriction of `ν` to `𝓕` -/
@[ext]
structure MeasureOnSpace (Ω : Type*) where
  ms : MeasurableSpace Ω
  μ : Measure[ms] Ω

/- Helper function to restrict the finer `MeasureOnSpace` to a coarser space -/
def MeasureOnSpace.restrict (m₁ : MeasureOnSpace Ω) (m₂ : MeasurableSpace Ω) : MeasureOnSpace Ω := {
  ms := m₂
  μ := m₁.μ.cast _
}

instance (Ω : Type*) : Preorder (MeasureOnSpace Ω) where
  le (ps₁ ps₂) := ps₁.ms ≤ ps₂.ms ∧ ps₁.μ = ps₂.μ.cast _
  le_refl := by simp
  le_trans (h₁ h₂) := by
    aesop (add safe forward le_trans) (add safe (by rw [MeasureTheory.Measure.map_map]))

def PSpace (Ω : Type*) :=
  {m : MeasureOnSpace Ω | IsProbabilityMeasure m.μ}

instance (Ω : Type*) : Preorder (PSpace Ω) where
  le (ps₁ ps₂) := (ps₁.1.ms ≤ ps₂.1.ms) ∧ ps₁.1.μ = ps₂.1.μ.cast _
  le_refl := by simp
  le_trans {a b c} (h₁ h₂) := by
    aesop (add safe forward le_trans) (add safe (by rw [MeasureTheory.Measure.map_map]))

abbrev PSp (Ω : Type*) := WithTop (PSpace Ω)

/-- Holds if `r` is the independent product of `p` and `q` -/
def PSpace.isIndependentProduct (r p q : PSpace Ω) :=
  r.1.ms = MeasurableSpace.sum p.1.ms q.1.ms ∧
  let μ₁ := p.1.μ
  let μ₂ := q.1.μ
  let μ := r.1.μ
  ∀ E (_ : MeasurableSet[p.1.ms] E)
    F (_ : MeasurableSet[q.1.ms] F),
  μ (E ∩ F) = μ₁ E * μ₂ F

open PSpace

lemma PSPace.ms_eq_of_isIndependentProduct {r r' p q : PSpace Ω}
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

/-- Every set in the generating set `w` is of the form `u ∩ v` -/
lemma exists_inter_measurableSet_of_mem_generator (w : Set Ω) (hw : w ∈ generator p q) :
  ∃ u v, w = u ∩ v ∧ MeasurableSet[p.ms] u ∧ MeasurableSet[q.ms] v := by
  rcases hw with ⟨u, v, rfl, hu, hv⟩
  grind

lemma mem_generator_l (u : Set Ω) (hu : MeasurableSet[p.ms] u) :
  u ∈ generator p q := by
  apply Exists.intro u
  apply Exists.intro ⊤
  simp
  apply hu

lemma mem_generator_r (u : Set Ω) (hu : MeasurableSet[q.ms] u) :
  u ∈ generator p q := by
  apply Exists.intro ⊤
  apply Exists.intro u
  simp
  apply hu

lemma inter_mem_generator {u v}
  (hu : MeasurableSet[p.ms] u) (hv : MeasurableSet[q.ms] v) :
  u ∩ v ∈ generator p q := by
  apply Exists.intro u
  apply Exists.intro v
  aesop

theorem MeasureOnSpace.generateFrom_generator_eq_sum :
  MeasurableSpace.generateFrom (generator p q) = p.ms.sum q.ms := by
  ext s
  constructor
  {
    apply MeasurableSpace.generateFrom_le
    simp
    intro _ he
    rcases he with ⟨u, ⟨v, helem, hu, hv⟩⟩
    have h₁ : u ∩ v ∈ generator p q := by
      apply Exists.intro u; apply Exists.intro v; aesop
    have h₂ : generator p q ⊆ MeasurableSet[MeasurableSpace.sum p.ms q.ms] := by
      intro u hu
      have hmatch : ∃ u₁ v₁, u = u₁ ∩ v₁ ∧ MeasurableSet[p.ms] u₁ ∧ MeasurableSet[q.ms] v₁ :=
        exists_inter_measurableSet_of_mem_generator p q u hu
      rcases hmatch with ⟨u₁, v₁, rfl, hu₁, hv₁⟩
      have hu₁meas : MeasurableSet[MeasurableSpace.sum p.ms q.ms] u₁ := by
        apply MeasurableSpace.measurableSet_generateFrom; aesop
      have hv₁meas : MeasurableSet[MeasurableSpace.sum p.ms q.ms] v₁ := by
        apply MeasurableSpace.measurableSet_generateFrom; aesop
      apply MeasurableSet.inter hu₁meas hv₁meas
    have h₃ : MeasurableSet[MeasurableSpace.generateFrom (generator p q)] (u ∩ v) := by
      apply MeasurableSpace.measurableSet_generateFrom; grind
    apply MeasurableSpace.generateFrom_le
    exact h₂
    rw [← helem] at h₃
    exact h₃
  }
  {
    apply MeasurableSpace.generateFrom_mono
    intro E hE
    rcases hE with h₁ | h₂
    apply mem_generator_l p q E h₁
    apply mem_generator_r p q E h₂
  }

lemma MeasureOnSpace.isPiSystem_generator : IsPiSystem (generator p q) := by
  intros u h_u v h_v _
  let ⟨u₁, u₂, prf_u, h_u1, h_u2⟩ := exists_inter_measurableSet_of_mem_generator p q u h_u
  let ⟨v₁, v₂, prf_v, h_v1, h_v2⟩ := exists_inter_measurableSet_of_mem_generator p q v h_v
  subst u v
  have h : (u₁ ∩ u₂) ∩ (v₁ ∩ v₂) = (u₁ ∩ v₁) ∩ (u₂ ∩ v₂) := by grind
  rw [h]
  apply inter_mem_generator
  simp_all only [MeasurableSet.inter]
  simp_all only [MeasurableSet.inter]

end GeneratingPiSystem

section Uniqueness

lemma MeasurableSpace.eq_cast_ext_ext
  {m₁ m₂ : MeasurableSpace Ω}
  (μ : Measure[m₁] Ω) (ν : Measure[m₂] Ω)
  (h_eq : m₁ = m₂) (h₂ : ∀ w, MeasurableSet[m₁] w → μ w = ν w) :
  μ = ν.cast _ := by
  subst h_eq
  ext1 E h_E
  rw [h₂]
  congr
  simp
  assumption

@[ext]
lemma MeasureOnSpace.ext_ms {p q : MeasureOnSpace Ω}
  (h_eq_alg : p.ms = q.ms)
  (h_eq_mea : ∀ E, MeasurableSet[p.ms] E → p.μ E = q.μ E) :
  p = q := by
  rcases p with ⟨f, m⟩
  rcases q with ⟨g, n⟩
  have h₁ := MeasurableSpace.eq_cast_ext_ext m n h_eq_alg h_eq_mea
  subst h_eq_alg
  simp_all only [Measure.map_id, implies_true]

@[ext]
lemma PSpace.ext_ms {p q : PSpace Ω}
  (h_eq_alg : p.1.ms = q.1.ms)
  (h_eq_mea : ∀ E, MeasurableSet[p.1.ms] E → p.1.μ E = q.1.μ E) :
  p = q := by
  rcases p with ⟨a, _⟩
  rcases q with ⟨b, _⟩
  have : a = b := MeasureOnSpace.ext_ms h_eq_alg h_eq_mea
  aesop

lemma PSpace.measure_ne_top (m : PSpace Ω) (u : Set Ω) : m.1.μ u ≠ ⊤ := by
  apply ne_of_lt
  have h₁ : m.1.μ Set.univ = 1 := m.2.measure_univ
  have h₂ : u ⊆ Set.univ := by aesop
  have h₃ : m.1.μ u ≤ m.1.μ Set.univ := measure_mono (μ := m.1.μ) h₂
  rw [h₁] at h₃
  apply lt_of_le_of_lt (b := 1) (c := (⊤ : ENNReal))
  simp_all only [Set.subset_univ]
  simp_all only [Set.subset_univ, ENNReal.one_lt_top]

theorem PSPace.uniqueness {r r' p q : PSpace Ω}
  (h₁ : isIndependentProduct r p q) (h₂ : isIndependentProduct r' p q) : r = r' := by
  apply PSpace.ext_ms
  rw [h₁.1, h₂.1]
  have : IsPiSystem (generator p.1 q.1) := MeasureOnSpace.isPiSystem_generator p.1 q.1
  -- Applying the π-λ theorem: the σ-algebra is by definition a λ-system,
  -- so we just need to show that the measures agree on a generating π-system
  apply MeasurableSpace.induction_on_inter
  assumption
  rw [MeasureTheory.measure_empty, MeasureTheory.measure_empty]
  {
    intro t h_t
    let ⟨u, v, prf, h_u, h_v⟩ := exists_inter_measurableSet_of_mem_generator p.1 q.1 t h_t
    rcases h₁ with ⟨h11, comb1⟩
    rcases h₂ with ⟨h21, comb2⟩
    rw [prf]
    have : r.1.μ (u ∩ v) = p.1.μ u * q.1.μ v := by
      apply comb1 u h_u v h_v
    have : r'.1.μ (u ∩ v) = p.1.μ u * q.1.μ v := by
      apply comb2 u h_u v h_v
    grind
  }
  {
    intro u h_u prf
    rcases h₁ with ⟨h1', comb1⟩
    rcases h₂ with ⟨h2', comb2⟩
    have isprob₁ : r.1.μ Set.univ = 1 := r.2.measure_univ
    have isprob₂ : r'.1.μ Set.univ = 1 := r'.2.measure_univ
    have h : r.1.ms = r'.1.ms := by grind
    have hu' : MeasurableSet[r'.1.ms] u := by
      apply MeasurableSpace.cast r.1.ms r'.1.ms
      assumption
      assumption
    have not_inf : r.1.μ u ≠ ⊤ := measure_ne_top r u
    have not_inf2 : r'.1.μ u ≠ ⊤ := measure_ne_top r' u
    have : r.1.μ uᶜ = 1 - r.1.μ u := by
      rw [MeasureTheory.measure_compl h_u not_inf, isprob₁]
    have : r'.1.μ uᶜ = 1 - r'.1.μ u := by
      rw [MeasureTheory.measure_compl hu' not_inf2, isprob₂]
    grind
  }
  {
    intro us disjoint hus prf
    have h_sum1 : r.1.μ (⋃ i, us i) = ∑' i, r.1.μ (us i) := by
      apply @Measure.m_iUnion (α := Ω) (f := us) r.1.ms r.1.μ hus disjoint
    have h_us' : ∀ i, MeasurableSet[r'.1.ms] (us i) := by
      intro i
      apply MeasurableSpace.cast r.1.ms
      apply PSPace.ms_eq_of_isIndependentProduct h₁ h₂
      exact (hus i)
    have : r'.1.μ (⋃ i, us i) = ∑' i, r'.1.μ (us i) := by
      apply @Measure.m_iUnion (α := Ω) (f := us) r'.1.ms r'.1.μ h_us' disjoint
    grind
  }
  {
    rcases h₁ with ⟨h₁, comb₁⟩
    rw [h₁]
    have := MeasureOnSpace.generateFrom_generator_eq_sum p.1 q.1
    grind
  }

end Uniqueness
