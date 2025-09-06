import Mathlib
import Iris
import Bluebell.Algebra.Probability
import Bluebell.Algebra.Permission
import Bluebell.Algebra.PSpPm
import Bluebell.Algebra.HyperAssertion

namespace Bluebell

open Iris ProbabilityTheory MeasureTheory HyperAssertion

variable {I α V F : Type*} [Nonempty V] [UFraction F]

-- /-- Order on the IndexedPSpPm is CMRA inclusion. -/
-- noncomputable instance : LE (IndexedPSpPm I α V F) := instLE_bluebell

noncomputable section

/-- Ownership of an indexed tuple of probability spaces `P : I → ProbabilitySpace (α → V)`
and permissions `p : I → Permission α F`, given compatibility witnesses. -/
def ownIndexedTuple (P : I → ProbabilityTheory.ProbabilitySpace (α → V)) (p : I → Permission α F) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun h : ∀ i, ProbabilityTheory.ProbabilitySpace.compatiblePerm (P i) (p i) =>
    own (M := IndexedPSpPm I α V F) (fun i => ⟨⟨WithTop.some (P i), p i⟩, h i⟩))

/-- Ownership of an indexed probability spaces `P : I → ProbabilitySpace (α → V)`,
defined as the existence of a compatible indexed permission. -/
def ownIndexedProb (P : I → ProbabilityTheory.ProbabilitySpace (α → V)) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun p : I → Permission α F => ownIndexedTuple (I := I) (α := α) (V := V) (F := F) P p)

variable [DecidableEq I] [Nonempty V]

/-- The hyper-assertion `E⟨i⟩ ∼ μ`. -/
def assertSampledFrom {β : Type*} [MeasurableSpace β] (i : I) (E : (α → V) → β) (μ : PMF β) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun P : I → ProbabilityTheory.ProbabilitySpace (α → V) =>
    sep (ownIndexedProb (I := I) (α := α) (V := V) (F := F) P)
      (pure (@AEMeasurable _ _ _ (P i).σAlg E (P i).μ ∧
        μ.toMeasure = @Measure.map _ _ (P i).σAlg _ E (P i).μ)))

/-- Assertion that the expected value of `E` at index `i` is `ev`. -/
def assertExpectation {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [AddCommMonoid β] [SMul ENNReal β]
    (i : I) (E : (α → V) → β) (ev : β) : HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun μ => sep (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)
    (pure (ev = ∑' b, (μ b) • b)))

/-- Assertion that the probability of a Boolean-valued expression `E` at index `i` is `prob`. -/
def assertProbability (i : I) (E : (α → V) → Bool) (prob : ENNReal) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun μ => sep (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)
    (pure (prob = μ true)))

/-- Assertion that `E` is true almost surely. -/
noncomputable def assertTrue (i : I) (E : (α → V) → Bool) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E (PMF.pure true)

/-- Assertion that we own `E` (but its distribution is not known). -/
def assertOwn {β : Type*} [MeasurableSpace β] (i : I) (E : (α → V) → β) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun μ => assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)

/-- Assertion that the variable `x : α` at index `i` has permission `q : Frac F`. -/
def assertPermissionVar (i : I) (x : α) (q : Frac F) : HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun Pp : IndexedPSpPm I α V F =>
    sep (own (M := IndexedPSpPm I α V F) Pp)
        (pure ((Pp i).1.2 x = DFrac.own (q : F))))

/-- Conjoin a `P` with ownership derived from a compatible `p`. -/
def assertPermission (P : HyperAssertion (IndexedPSpPm I α V F)) (p : I → Permission α F) : HyperAssertion (IndexedPSpPm I α V F) :=
  and P <|
    «exists»
      (fun compatP :
        {P : I → ProbabilityTheory.ProbabilitySpace (α → V) //
          ∀ i, ProbabilityTheory.ProbabilitySpace.compatiblePerm (P i) (p i)} =>
      own (M := IndexedPSpPm I α V F) (fun i => ⟨⟨WithTop.some (compatP.1 i), p i⟩, compatP.2 i⟩))

end

open HyperAssertion

variable {I α V F : Type*} [Nonempty V] [UFraction F]

/-! ### Ownership rules (moved from Basic) -/

section Rules

variable [DecidableEq I]

/-- If `P` and `Q` affect disjoint sets of indices, then `P ∧ Q` entails `P ∗ Q`. -/
theorem sep_of_and [Fintype I]
    {P Q : HyperAssertion (IndexedPSpPm I α V F)}
    (h : HyperAssertion.relevantIndices (I := I) P ∩
         HyperAssertion.relevantIndices (M := PSpPm α V F) (I := I) Q = ∅) :
    HyperAssertion.entails (HyperAssertion.and P Q) (HyperAssertion.sep P Q) := by
  sorry

/-- If `E⟨i⟩` is sampled from both `μ` and `μ'`, then `⌜ μ = μ' ⌝` holds as a proposition. -/
theorem sampledFrom_inj {β : Type*} [MeasurableSpace β]
    {i : I} {E : (α → V) → β} {μ μ' : PMF β} :
    HyperAssertion.entails
      (HyperAssertion.and
        (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)
        (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ'))
      (HyperAssertion.pure (μ = μ')) := by
  sorry

/-- `E₁⟨i⟩` and `E₂⟨i⟩` are both true iff `E₁⟨i⟩ ∧ E₂⟨i⟩` is true. -/
theorem sep_assertTrue_iff {i : I} {E₁ E₂ : (α → V) → Bool} :
    HyperAssertion.equiv
      (HyperAssertion.sep
        (assertTrue (I := I) (α := α) (V := V) (F := F) i E₁)
        (assertTrue (I := I) (α := α) (V := V) (F := F) i E₂))
      (assertTrue (I := I) (α := α) (V := V) (F := F) i (fun x => E₁ x ∧ E₂ x)) := by
  sorry

/-- If `pabs(𝑃, pvar(𝐸⟨𝑖⟩))` (to be defined), then `assertTrue i E ∧ P` entails `assertTrue i E ∗ P`. -/
theorem sep_of_and_assertTrue {i : I} {E : (α → V) → Bool}
    {P : HyperAssertion (IndexedPSpPm I α V F)} (h : True) :
    HyperAssertion.entails
      (HyperAssertion.sep
        (assertTrue (I := I) (α := α) (V := V) (F := F) i E)
        P)
      (HyperAssertion.and
        (assertTrue (I := I) (α := α) (V := V) (F := F) i E)
        P) := by
  sorry

/-- Sampling on a product splits into sampling each component. -/
theorem sampledFrom_prod {β₁ β₂ : Type _}
    [MeasurableSpace β₁] [MeasurableSpace β₂] {i : I}
    (E₁ : (α → V) → β₁) (E₂ : (α → V) → β₂)
    (μ₁ : PMF β₁) (μ₂ : PMF β₂) :
    HyperAssertion.entails
      (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i (fun x => (E₁ x, E₂ x))
        (Prod.mk <$> μ₁ <*> μ₂))
      (HyperAssertion.sep
        (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E₁ μ₁)
        (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E₂ μ₂)) := by
  sorry

end Rules

end Bluebell

#min_imports
