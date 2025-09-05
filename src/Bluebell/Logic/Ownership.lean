import Iris
import Bluebell.Algebra.Probability
import Bluebell.Algebra.Permission
import Bluebell.Algebra.PSpPm
import Bluebell.Algebra.HyperAssertion

namespace Bluebell

open Iris ProbabilityTheory MeasureTheory HyperAssertion

variable {I α V F : Type*} [UFraction F]

/-- Model carrier for ownership assertions. -/
abbrev Model (I α V F : Type*) [UFraction F] := IndexedPSpPm I α V F

/-- Temporary preorder on the model to enable `HyperAssertion` over it. -/
scoped instance : LE (Model I α V F) := ⟨fun _ _ => True⟩

/-- Ownership of an indexed tuple of probability spaces `P : I → ProbabilitySpace (α → V)`
and permissions `p : I → Permission α F`, given compatibility witnesses. -/
def ownIndexedTuple (P : I → ProbabilityTheory.ProbabilitySpace (α → V))
    (p : I → Permission α F) : HyperAssertion (Model I α V F) :=
  «exists» (fun _h : ∀ i, ProbabilityTheory.ProbabilitySpace.compatiblePerm (P i) (p i) =>
    pure True)

/-- Ownership of an indexed probability spaces `P : I → ProbabilitySpace (α → V)`,
defined as the existence of a compatible indexed permission. -/
def ownIndexedProb (P : I → ProbabilityTheory.ProbabilitySpace (α → V)) : HyperAssertion (Model I α V F) :=
  «exists» (fun p : I → Permission α F => ownIndexedTuple (I := I) (α := α) (V := V) (F := F) P p)

variable [DecidableEq I] [Nonempty V]

/-- The hyper-assertion `E⟨i⟩ ∼ μ`. -/
def assertSampledFrom {β : Type*} [MeasurableSpace β]
    (i : I) (E : (α → V) → β) (μ : PMF β) : HyperAssertion (Model I α V F) :=
  «exists» (fun P : I → ProbabilityTheory.ProbabilitySpace (α → V) =>
    and (ownIndexedProb (I := I) (α := α) (V := V) (F := F) P)
      (pure (@AEMeasurable _ _ _ (P i).σAlg E (P i).μ ∧
        μ.toMeasure = @Measure.map _ _ (P i).σAlg _ E (P i).μ)))

/-- Assertion that the expected value of `E` at index `i` is `ev`. -/
def assertExpectation {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [AddCommMonoid β] [SMul ENNReal β]
    (i : I) (E : (α → V) → β) (ev : β) : HyperAssertion (Model I α V F) :=
  «exists» (fun μ => and (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)
    (pure (ev = ∑' b, (μ b) • b)))

/-- Assertion that the probability of a Boolean-valued expression `E` at index `i` is `prob`. -/
def assertProbability (i : I) (E : (α → V) → Bool) (prob : ENNReal) : HyperAssertion (Model I α V F) :=
  «exists» (fun μ => and (assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)
    (pure (prob = μ true)))

/-- Assertion that `E` is true almost surely. -/
noncomputable def assertTrue (i : I) (E : (α → V) → Bool) : HyperAssertion (Model I α V F) :=
  assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E (PMF.pure true)

/-- Assertion that we own `E` (but its distribution is not known). -/
def assertOwn {β : Type*} [MeasurableSpace β] (i : I) (E : (α → V) → β) : HyperAssertion (Model I α V F) :=
  «exists» (fun μ => assertSampledFrom (I := I) (α := α) (V := V) (F := F) i E μ)

/-- Assertion that the variable `x : α` at index `i` has permission `q : Frac F`. -/
def assertPermissionVar (i : I) (x : α) (q : Frac F) : HyperAssertion (Model I α V F) :=
  «exists» (fun Pp : IndexedPSpPm I α V F => and (pure True) (pure ((Pp i).1.2 x = DFrac.own (q : F))))

/-- Conjoin a `P` with ownership derived from a compatible `p`. -/
def assertPermission (P : HyperAssertion (Model I α V F)) (p : I → Permission α F) : HyperAssertion (Model I α V F) :=
  .and P <|
    «exists» (fun compatP : {P : I → ProbabilityTheory.ProbabilitySpace (α → V) // ∀ i, ProbabilityTheory.ProbabilitySpace.compatiblePerm (P i) (p i)} =>
      pure True)

end Bluebell
