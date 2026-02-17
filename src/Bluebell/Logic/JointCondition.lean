import Iris
import Bluebell.Algebra.PSpPm
import Bluebell.Algebra.HyperAssertion
import Bluebell.Logic.Ownership
import Bluebell.ProbabilityTheory.IndepProduct

open Iris ProbabilityTheory

namespace Bluebell
namespace HyperAssertion

variable {I α V : Type*} [Nonempty V]

/-!
`jointCondition` implements the modality from the paper (logic.tex, Def. "Supercond modality").

Paper definition (informal Lean transcription):
- Given `μ : PMF β` and `K : β → HAssrt_I`, define
  `C_ μ K : HAssrt_I` to hold on a resource `a` iff there exist
  σ-algebras/measures `σF, μs`, permissions `permap`, and a kernel `κ` s.t.
  1. `(σF, μs, permap) ≤ a` (RA inclusion),
  2. ∀ i, `μs i = bind μ (κ i)`, and
  3. ∀ v ∈ support(μ), `K v (σF, (λ i, κ i v), permap)`.

Our encoding over the model `IndexedPSpPmRat I α V` realizes these components as:
- `P : I → ProbabilitySpace (α → V)` packs per-index `(σAlg, μ)`,
- `p : I → PermissionRat α`,
- `κ : (i : I) → β → Measure (α → V)` (a Markov kernel into the common outcome space),
- we assemble resources as tuples `⟨psp, perm, compat⟩` and require
  CMRA inclusion into the current `a`.

Formal statement as used here:
`a ∈ C_ μ K` iff there exist `P p h κ` such that
- `(fun i => ⟨WithTop.some (P i), p i, h i⟩) ≤ a`,
- `∀ i, (P i).μ = μ.toMeasure.bind (κ i)`,
- `∀ v ∈ μ.support, K v (fun j => ⟨WithTop.some (ProbabilitySpace.mk (MeasureSpace.mk (P j).σAlg (κ j v)) …), p j, h j⟩)`.

Current stubs/assumptions in this implementation:
- We do not prove that each `κ i v` is a probability measure; this appears as a
  `sorry` for `IsProbabilityMeasure` when constructing `ProbabilitySpace.mk`.
- We do not state measurability assumptions on `κ` (kernel laws) explicitly;
  those can be added later as hypotheses if needed.
- Compatibility proofs for the kernel-updated spaces are discharged by
  `simp` using our `compatiblePermRat` definition (insensitivity of the σ-algebra),
  which is correct under the paper's intent, but stronger facts (e.g. closure)
  will be proved in subsequent work.
- The order `≤` on the model is `CMRA.Included` (see HyperAssertion wiring).
- All deeper properties are intentionally left as theorem statements with `sorry`.
-/
noncomputable def jointCondition {β : Type*} [MeasurableSpace β] [MeasurableSpace V]
    (μ : PMF β) (K : β → HyperAssertion (IndexedPSpPmRat I α V)) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  ⟨setOf (fun a =>
    ∃ (P : I → ProbabilityTheory.ProbabilitySpace (α → V))
      (p : I → PermissionRat α)
      (h : ∀ i, PSp.compatiblePermRat (WithTop.some (P i)) (p i))
      (κ : (i : I) → β → @MeasureTheory.Measure (α → V) (P i).σAlg),
      -- Pack current owned resource and require inclusion into `a`
      (fun i => ⟨WithTop.some (P i), p i, h i⟩) ≼ a ∧
      -- Each index measure factors as μ bind κ(i)
      (∀ i, (P i).μ = μ.toMeasure.bind (κ i)) ∧
      -- For every outcome v of μ, K v holds on the tuple of kernels evaluated at v
      (∀ v ∈ μ.support,
        K v
          (fun j => ⟨WithTop.some
              (@ProbabilityTheory.ProbabilitySpace.mk _
                (@MeasureTheory.MeasureSpace.mk _ (P j).σAlg (κ j v))
                (by
                  -- IsProbabilityMeasure for the kernel measure at index j and outcome v
                  -- deferred as a placeholder
                  sorry)),
            p j,
            h j⟩))
    ), by
    -- Upward-closure: witnesses remain valid and inclusion composes.
    intro a a' haa' ha
    rcases ha with ⟨P, p, h, κ, hinc, hμ, hK⟩
    refine ⟨P, p, h, κ, CMRA.Included.trans hinc haa', hμ, hK⟩⟩

notation "𝑪_" => jointCondition

-- def isPermissionAbstract (X : Set (I × α)) (P : HyperAssertion (IndexedPSpPmRat I α V)) : Prop := sorry
  -- ∀ Pp : IndexedPSpPmRat I α V, ∀ q : ℚ≥0, ∀ n : ℕ+, P Pp ≤ P → ∃ Pp' : IndexedPSpPmRat I α V, Pp' ≤ P ∧ Pp = Pp' ∧ True

-- Lifting of a relation via the joint conditioning modality
noncomputable def liftRelation [Nonempty V] [DecidableEq V] [MeasurableSpace V]
    (s : _root_.Set (I × α)) (R : _root_.Set (s → V)) :
    HyperAssertion (IndexedPSpPmRat I α V) :=
  «exists» (fun μ : PMF (s → V) =>
    sep (pure (∑' x : R, μ x = 1))
      (𝑪_ μ (fun v : s → V =>
        «forall» (fun x : s => assertTrue x.1.1 (fun y => v x = y x.1.2)))))

section JointConditioning

variable {β : Type*} [MeasurableSpace β] {μ : PMF β}
  {K K₁ K₂ : β → HyperAssertion (IndexedPSpPmRat I α V)}
  [MeasurableSpace V]

theorem C_conseq (h : ∀ v, K₁ v ⊢ K₂ v) : 𝑪_ μ K₁ ⊢ 𝑪_ μ K₂ := by
  intro a ha
  obtain ⟨P, p, hc, κ, hinc, hμ, hK⟩ := ha
  exact ⟨P, p, hc, κ, hinc, hμ, fun v hv ↦ h v _ (hK v hv)⟩

theorem C_frame {P : HyperAssertion (IndexedPSpPmRat I α V)} :
    P ∗ 𝑪_ μ K ⊢ 𝑪_ μ (fun v => sep P (K v)) := by
  sorry

theorem C_unit_left [Countable β] [MeasurableSingletonClass β] {v₀ : β} :
    𝑪_ (MeasureTheory.Measure.dirac v₀).toPMF K ⊣⊢ K v₀ := by
  sorry

theorem C_unit_right [DecidableEq β] {i : I} {E : (α → V) → β} {μ : PMF β} :
    assertSampledFrom i E μ ⊣⊢ 𝑪_ μ (fun v => assertTrue i (fun x => E x = v)) := by
  sorry

theorem C_assoc {β₁ β₂ : Type _} [MeasurableSpace β₁] [MeasurableSpace β₂]
    {μ : PMF β₁} {κ : β₁ → PMF β₂}
    {K : β₁ × β₂ → HyperAssertion (IndexedPSpPmRat I α V)} :
      𝑪_ μ (fun v => 𝑪_ (κ v) (fun w => K (v, w))) ⊢
        𝑪_ (do let v ← μ; let w ← κ v; return (v, w)) K := by
  sorry

theorem C_unassoc {β₁ β₂ : Type _} [MeasurableSpace β₁] [MeasurableSpace β₂]
    {μ : PMF β₁} {κ : β₁ → PMF β₂}
    {K : β₂ → HyperAssertion (IndexedPSpPmRat I α V)} :
      𝑪_ (μ.bind κ) (fun w => K w) ⊢ 𝑪_ μ (fun v => 𝑪_ (κ v) (fun w => K w)) := by
  sorry

theorem C_and [DecidableEq I] [Fintype I]
    (h : ∀ v, relevantIndices (K₁ v) ∩ relevantIndices (K₂ v) = ∅) :
    𝑪_ μ K₁ ∧ 𝑪_ μ K₂ ⊢ 𝑪_ μ (fun v => and (K₁ v) (K₂ v)) := by
  sorry

/-- Also requires that the measurable space on `β` is the top one -/
theorem C_exists {γ : Type*}
    {Q : β × γ → HyperAssertion (IndexedPSpPmRat I α V)} :
    𝑪_ μ (fun v => ∃ x, Q (v, x)) ⊢ ∃ f : β → γ, 𝑪_ μ (fun v => Q (v, f v)) := by
  sorry

theorem C_forall {γ : Type*}
    {Q : β × γ → HyperAssertion (IndexedPSpPmRat I α V)} :
    𝑪_ μ (fun v => «forall» (fun x => Q (v, x))) ⊢ ∀ x, 𝑪_ μ (fun v => Q (v, x)) := by
  sorry

theorem C_transfer {β' : Type*} [MeasurableSpace β'] {μ' : PMF β'}
    (f : μ'.support ≃ μ.support)
    (h : ∀ b, (hb : b ∈ μ'.support) → μ' b = μ (f ⟨b, hb⟩).1) :
      𝑪_ μ K ⊢ 𝑪_ μ' (fun b => K (f ⟨b, sorry⟩)) := by
  sorry

theorem C_sep_assertTrue {i : I} {E : (α → V) → Bool} :
    𝑪_ μ (fun v => sep (K v) (assertTrue i E)) ⊢ assertTrue i E ∗ 𝑪_ μ K := by
  sorry

theorem C_pure {s : _root_.Set β} :
    ⌜ ∑' x : s, μ x = 1 ⌝ ∗ 𝑪_ μ K ⊣⊢ 𝑪_ μ (fun v => sep (pure (v ∈ s)) (K v)) := by
  sorry

end JointConditioning

end HyperAssertion
end Bluebell
