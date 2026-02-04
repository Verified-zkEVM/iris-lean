import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! ## Independent product of probability measures -/

open ProbabilityTheory MeasureTheory

alias MeasureTheory.MeasureSpace.σAlg := MeasureSpace.toMeasurableSpace
alias MeasureTheory.MeasureSpace.μ := MeasureSpace.volume

variable {Ω : Type*}

noncomputable section

namespace MeasureTheory

@[simp]
abbrev Measure.map! (ms₁ : MeasurableSpace α) (ms₂ : MeasurableSpace β)
                    (f : α → β) (μ : Measure α) : Measure β := @μ.map _ _ ms₁ ms₂ f

@[simp]
abbrev Measure.cast {β : Type u} {ms₁ : MeasurableSpace β}
  (μ : Measure β) (ms₂ : MeasurableSpace β) := μ.map! ms₁ ms₂ id

@[simp]
def sum (m1 : MeasurableSpace Ω) (m2 : MeasurableSpace Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom (MeasurableSet[m1] ∪ MeasurableSet[m2])

def measurable_set_transport
  (m₁ m₂ : MeasurableSpace Ω) (p : m₁ = m₂) (E : Set Ω)
  (h : MeasurableSet[m₁] E) : MeasurableSet[m₂] E := by
  subst p
  simp_all only

end MeasureTheory

end noncomputable section

/- We define `(𝓕, μ) ≤ (𝓖, ν)` if `𝓕 ⊆ 𝓖` and `μ` is the restriction of `ν` to `𝓕` -/
@[ext]
structure MeasureOnSpace (Ω : Type u) where
  ms : MeasurableSpace Ω
  μ : Measure[ms] Ω

/- Helper function to restrict the finer `MeasureOnSpace` to a coarser space -/
def MeasureOnSpace.restrict (m₁ : MeasureOnSpace Ω) (m₂ : MeasurableSpace Ω)
  : MeasureOnSpace Ω := {
  ms := m₂
  μ := m₁.μ.cast _
}

instance (Ω : Type*) : Preorder (MeasureOnSpace Ω) where
  le (ps₁ ps₂) := ps₁.ms ≤ ps₂.ms ∧ ps₁.μ = ps₂.μ.cast _
  le_refl := by simp
  le_trans (h₁ h₂) := by
    aesop (add safe forward le_trans) (add safe (by rw [MeasureTheory.Measure.map_map]))

def PSpace (Ω : Type u) :=
  {m : MeasureOnSpace Ω | IsProbabilityMeasure m.μ}

instance (Ω : Type*) : Preorder (PSpace Ω) where
  le (ps₁ ps₂) := (ps₁.1.ms ≤ ps₂.1.ms) ∧ ps₁.1.μ = ps₂.1.μ.cast _
  le_refl := by simp
  le_trans {a b c} (h₁ h₂) := by
    aesop (add safe forward le_trans) (add safe (by rw [MeasureTheory.Measure.map_map]))

abbrev PSp (Ω : Type u) := WithTop (PSpace Ω)

/- Holds if `r` is the independent product of `p` and `q` -/
def isIndependentProduct (r p q : PSpace Ω) :=
  r.1.ms = MeasureTheory.sum p.1.ms q.1.ms ∧
  let μ₁ := p.1.μ
  let μ₂ := q.1.μ
  let μ := r.1.μ
  ∀ E (_ : MeasurableSet[p.1.ms] E)
    F (_ : MeasurableSet[q.1.ms] F),
  μ (E ∩ F) = μ₁ E * μ₂ F

lemma MeasureOnSpace.indep_prod_has_same_measurable_set
  (h1 : isIndependentProduct r p q) (h2 : isIndependentProduct r' p q) :
  r.1.ms = r'.1.ms := by
  rcases h1 with ⟨a, _⟩
  rcases h2 with ⟨c, _⟩
  aesop

section GeneratingPiSystem

variable {Ω : Type*} (p q : MeasureOnSpace Ω)

/-
  Given `p q : MeasureOnSpace Ω`, `generator p q` is a set of subsets of Ω that
  generates the smallest σ-algebra containing both σ-algebras
-/
def generator (p q : MeasureOnSpace Ω) : Set (Set Ω) :=
  {S : Set Ω | ∃ F G, S = F ∩ G ∧ MeasurableSet[p.ms] F ∧ MeasurableSet[q.ms] G}

/- Every set in the generating set `w` is of the form `u ∩ v` -/
lemma generator_pattern_match (w : Set Ω) (h_w : w ∈ generator p q) :
  ∃ u v, w = u ∩ v ∧ MeasurableSet[p.ms] u ∧ MeasurableSet[q.ms] v := by
  rcases h_w with ⟨u, v, rfl, h_u, h_v⟩
  grind

lemma generator_contain_first (u : Set Ω) (h_u : MeasurableSet[p.ms] u)
  : u ∈ generator p q := by
  apply Exists.intro u
  apply Exists.intro ⊤
  simp
  apply h_u

lemma generator_contain_second (u : Set Ω) (h_u : MeasurableSet[q.ms] u)
  : u ∈ generator p q := by
  apply Exists.intro ⊤
  apply Exists.intro u
  simp
  apply h_u

lemma generator_elem
  (h_u : MeasurableSet[p.ms] u) (h_v : MeasurableSet[q.ms] v)
  : u ∩ v ∈ generator p q := by
  apply Exists.intro u
  apply Exists.intro v
  aesop

theorem generator_generates_independent_sigma_algebra :
  MeasurableSpace.generateFrom (generator p q) = MeasureTheory.sum p.ms q.ms := by
  ext s
  constructor
  {
    apply MeasurableSpace.generateFrom_le
    simp
    intro _ h_e
    rcases h_e with ⟨u, ⟨v, h_elem, h_u, h_v⟩⟩
    have h1 : u ∩ v ∈ generator p q := by
      apply Exists.intro u; apply Exists.intro v; aesop
    have h2 : generator p q ⊆ MeasurableSet[MeasureTheory.sum p.ms q.ms] := by
      intro u h_u
      have h_match : ∃ u1 v1, u = u1 ∩ v1 ∧ MeasurableSet[p.ms] u1 ∧ MeasurableSet[q.ms] v1 :=
        generator_pattern_match p q u h_u
      rcases h_match with ⟨u1, v1, rfl, h_u1, h_v1⟩
      have h_u1_meas : MeasurableSet[MeasureTheory.sum p.ms q.ms] u1 := by
        apply MeasurableSpace.measurableSet_generateFrom; aesop
      have h_v1_meas : MeasurableSet[MeasureTheory.sum p.ms q.ms] v1 := by
        apply MeasurableSpace.measurableSet_generateFrom; aesop
      apply MeasurableSet.inter h_u1_meas h_v1_meas
    have h3 : MeasurableSet[MeasurableSpace.generateFrom (generator p q)] (u ∩ v) := by
      apply MeasurableSpace.measurableSet_generateFrom; grind
    apply MeasurableSpace.generateFrom_le
    exact h2
    rw [← h_elem] at h3
    exact h3
  }
  {
    apply MeasurableSpace.generateFrom_mono
    intro E hE
    rcases hE with h1 | h2
    apply generator_contain_first p q E h1
    apply generator_contain_second p q E h2
  }

lemma generator_is_pi_system : IsPiSystem (generator p q) := by
  intros u h_u v h_v _
  let ⟨u1, u2, prf_u, h_u1, h_u2⟩ := generator_pattern_match p q u h_u
  let ⟨v1, v2, prf_v, h_v1, h_v2⟩ := generator_pattern_match p q v h_v
  subst u v
  have h : (u1 ∩ u2) ∩ (v1 ∩ v2) = (u1 ∩ v1) ∩ (u2 ∩ v2) := by grind
  rw [h]
  apply generator_elem
  simp_all only [MeasurableSet.inter]
  simp_all only [MeasurableSet.inter]

end GeneratingPiSystem

section Uniqueness

lemma measure_heterogeneous_ext
  {m1 m2 : MeasurableSpace Ω}
  (μ : Measure[m1] Ω) (ν : Measure[m2] Ω)
  (h_eq : m1 = m2) (h2 : ∀ w, MeasurableSet[m1] w → μ w = ν w)
  : μ = @Measure.map Ω Ω m2 m1 id ν := by
  subst h_eq
  ext1 E h_E
  rw [h2]
  congr
  rw [Measure.map_id]
  assumption

@[ext]
lemma measure_on_space_ext {p q : MeasureOnSpace Ω}
  (h_eq_alg : p.ms = q.ms)
  (h_eq_mea : ∀ E, MeasurableSet[p.ms] E → p.μ E = q.μ E)
  : p = q := by
  rcases p with ⟨f, m⟩
  rcases q with ⟨g, n⟩
  have h1 := measure_heterogeneous_ext m n h_eq_alg h_eq_mea
  subst h_eq_alg
  simp_all only [Measure.map_id, implies_true]

@[ext]
lemma pspace_ext {p q : PSpace Ω}
  (h_eq_alg : p.1.ms = q.1.ms)
  (h_eq_mea : ∀ E, MeasurableSet[p.1.ms] E → p.1.μ E = q.1.μ E)
  : p = q := by
  rcases p with ⟨a, _⟩
  rcases q with ⟨b, _⟩
  have : a = b := measure_on_space_ext h_eq_alg h_eq_mea
  aesop

lemma pspace_not_inf (m : PSpace Ω) (u : Set Ω)
  : m.1.μ u ≠ ⊤ := by
  apply ne_of_lt
  have h1 : m.1.μ Set.univ = 1 := m.2.measure_univ
  have h2 : u ⊆ Set.univ := by aesop
  have h3 : m.1.μ u ≤ m.1.μ Set.univ := measure_mono (μ := m.1.μ) h2
  rw [h1] at h3
  apply lt_of_le_of_lt (b := 1) (c := (⊤ : ENNReal))
  simp_all only [Set.subset_univ]
  simp_all only [Set.subset_univ, ENNReal.one_lt_top]

theorem uniqueness {r r' p q : PSpace Ω}
  (h1 : isIndependentProduct r p q) (h2 : isIndependentProduct r' p q)
  : r = r' := by
  apply pspace_ext
  rw [h1.1, h2.1]
  have : IsPiSystem (generator p.1 q.1) := generator_is_pi_system p.1 q.1
  -- Applying the π-λ theorem: the σ-algebra is by definition a λ-system,
  -- so we just need to show that the measures agree on a generating π-system
  apply MeasurableSpace.induction_on_inter
  assumption
  rw [MeasureTheory.measure_empty, MeasureTheory.measure_empty]
  {
    intro t h_t
    let ⟨u, v, prf, h_u, h_v⟩ := generator_pattern_match p.1 q.1 t h_t
    rcases h1 with ⟨h11, comb1⟩
    rcases h2 with ⟨h21, comb2⟩
    rw [prf]
    have : r.1.μ (u ∩ v) = p.1.μ u * q.1.μ v := by
      apply comb1 u h_u v h_v
    have : r'.1.μ (u ∩ v) = p.1.μ u * q.1.μ v := by
      apply comb2 u h_u v h_v
    grind
  }
  {
    intro u h_u prf
    rcases h1 with ⟨h1', comb1⟩
    rcases h2 with ⟨h2', comb2⟩
    have is_prob1 : r.1.μ Set.univ = 1 := r.2.measure_univ
    have is_prob2 : r'.1.μ Set.univ = 1 := r'.2.measure_univ
    have h : r.1.ms = r'.1.ms := by grind
    have h_u' : MeasurableSet[r'.1.ms] u := by
      apply measurable_set_transport r.1.ms r'.1.ms
      assumption
      assumption
    have not_inf : r.1.μ u ≠ ⊤ := pspace_not_inf r u
    have not_inf2 : r'.1.μ u ≠ ⊤ := pspace_not_inf r' u
    have : r.1.μ uᶜ = 1 - r.1.μ u := by
      rw [MeasureTheory.measure_compl h_u not_inf, is_prob1]
    have : r'.1.μ uᶜ = 1 - r'.1.μ u := by
      rw [MeasureTheory.measure_compl h_u' not_inf2, is_prob2]
    grind
  }
  {
    intro us disjoint h_us prf
    have h_sum1 : r.1.μ (⋃ i, us i) = ∑' i, r.1.μ (us i) := by
      apply @Measure.m_iUnion (α := Ω) (f := us) r.1.ms r.1.μ h_us disjoint
    have h_us' : ∀ i, MeasurableSet[r'.1.ms] (us i) := by
      intro i
      apply measurable_set_transport r.1.ms
      apply MeasureOnSpace.indep_prod_has_same_measurable_set h1 h2
      exact (h_us i)
    have : r'.1.μ (⋃ i, us i) = ∑' i, r'.1.μ (us i) := by
      apply @Measure.m_iUnion (α := Ω) (f := us) r'.1.ms r'.1.μ h_us' disjoint
    grind
  }
  {
    rcases h1 with ⟨h1, comb1⟩
    rw [h1]
    have := generator_generates_independent_sigma_algebra p.1 q.1
    grind
  }

end Uniqueness
