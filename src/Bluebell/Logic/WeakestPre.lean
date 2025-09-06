import Iris
import Bluebell.Algebra.PSpPm
import Bluebell.Algebra.HyperAssertion
import Bluebell.Logic.JointCondition

open Iris ProbabilityTheory

namespace Bluebell
namespace HyperAssertion

variable {I α V F : Type*} [Nonempty V] [MeasurableSpace V] [UFraction F]

/-- Weakest precondition of a program. TODO: stub for now -/
noncomputable def wp (t : IndexedPSpPm I α V F → IndexedPSpPm I α V F)
    (Q : HyperAssertion (IndexedPSpPm I α V F)) :
    HyperAssertion (IndexedPSpPm I α V F) :=
  ⟨setOf (fun a => ∀ μ₀ c, (a • c) ≤ IndexedPSpPm.liftProb μ₀ →
    ∃ b, (b • c) ≤ t (IndexedPSpPm.liftProb μ₀) ∧ Q b), by sorry⟩

variable {t t₁ t₂ : IndexedPSpPm I α V F → IndexedPSpPm I α V F}
  {P Q Q' Q₁ Q₂ : HyperAssertion (IndexedPSpPm I α V F)}

theorem wp_conseq (h : Q ⊢ Q') : (wp t Q) ⊢ (wp t Q') := by sorry

theorem wp_frame : P ∗ (wp t Q) ⊢ (wp t (sep P Q)) := by sorry

theorem wp_comp : (wp t₁ (wp t₂ Q)) ⊣⊢ (wp (t₁ ∘ t₂) Q) := by sorry

/-- TODO: `relevantIndices` of a program and program composition placeholder -/
theorem wp_conj : (wp t₁ Q₁) ∧ (wp t₂ Q₂) ⊣⊢ (wp (sorry) (and Q₁ Q₂)) := by sorry

/-- TODO: what is `own_α` exactly (`own_𝕏` in the paper)? -/
theorem C_wp_swap {β : Type*} [MeasurableSpace β] {μ : PMF β}
    {K : β → HyperAssertion (IndexedPSpPm I α V F)} :
    𝑪_ μ (fun v => wp t (K v)) ∧ sorry ⊢ wp t (𝑪_ μ K) := by sorry

end HyperAssertion
end Bluebell
