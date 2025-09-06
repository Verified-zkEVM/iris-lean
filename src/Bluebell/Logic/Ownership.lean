import Mathlib
import Iris
import Bluebell.Algebra.Probability
import Bluebell.Algebra.Permission
import Bluebell.Algebra.PSpPm
import Bluebell.Algebra.HyperAssertion

namespace Bluebell

open Iris ProbabilityTheory MeasureTheory HyperAssertion

variable {I α V F : Type*} [UFraction F]

-- /-- Order on the IndexedPSpPm is CMRA inclusion. -/
-- noncomputable scoped instance : LE (IndexedPSpPm I α V F) := inferInstance

noncomputable section

/-- Ownership of an indexed tuple of probability spaces `P : I → ProbabilitySpace (α → V)`
and permissions `p : I → Permission α F`, given compatibility witnesses. -/
def ownIndexedTuple (P : I → ProbabilityTheory.ProbabilitySpace (α → V))
    (p : I → Permission α F) : HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun h : ∀ i, ProbabilityTheory.ProbabilitySpace.compatiblePerm (P i) (p i) =>
    own (M := IndexedPSpPm I α V F)
      (fun i => ⟨⟨WithTop.some (P i), p i⟩,
        by
          simp [ProbabilityTheory.ProbabilitySpace.compatiblePerm]⟩))

/-- Ownership of an indexed probability spaces `P : I → ProbabilitySpace (α → V)`,
defined as the existence of a compatible indexed permission. -/
def ownIndexedProb (P : I → ProbabilityTheory.ProbabilitySpace (α → V)) : HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun p : I → Permission α F => ownIndexedTuple (I := I) (α := α) (V := V) (F := F) P p)

variable [DecidableEq I] [Nonempty V]

/-- The hyper-assertion `E⟨i⟩ ∼ μ`. -/
def assertSampledFrom {β : Type*} [MeasurableSpace β]
    (i : I) (E : (α → V) → β) (μ : PMF β) : HyperAssertion (IndexedPSpPm I α V F) :=
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
def assertProbability (i : I) (E : (α → V) → Bool) (prob : ENNReal) : HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun μ => sep (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)
    (pure (prob = μ true)))

/-- Assertion that `E` is true almost surely. -/
noncomputable def assertTrue (i : I) (E : (α → V) → Bool) : HyperAssertion (IndexedPSpPm I α V F) :=
  assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E (PMF.pure true)

/-- Assertion that we own `E` (but its distribution is not known). -/
def assertOwn {β : Type*} [MeasurableSpace β] (i : I) (E : (α → V) → β) : HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun μ => assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)

/-- Assertion that the variable `x : α` at index `i` has permission `q : Frac F`. -/
def assertPermissionVar (i : I) (x : α) (q : Frac F) : HyperAssertion (IndexedPSpPm I α V F) :=
  «exists» (fun Pp : IndexedPSpPm I α V F =>
    sep (own (M := IndexedPSpPm I α V F) Pp)
        (pure ((Pp i).1.2 x = DFrac.own (q : F))))

/-- Conjoin a `P` with ownership derived from a compatible `p`. -/
def assertPermission (P : HyperAssertion (IndexedPSpPm I α V F)) (p : I → Permission α F) : HyperAssertion (IndexedPSpPm I α V F) :=
  and P <|
    «exists» (fun compatP : {P : I → ProbabilityTheory.ProbabilitySpace (α → V) // ∀ i, ProbabilityTheory.ProbabilitySpace.compatiblePerm (P i) (p i)} =>
      own (M := IndexedPSpPm I α V F)
        (fun i => ⟨⟨WithTop.some (compatP.1 i), p i⟩,
          by
            simp [ProbabilityTheory.ProbabilitySpace.compatiblePerm]⟩))

end

end Bluebell
