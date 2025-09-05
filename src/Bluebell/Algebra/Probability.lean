import Bluebell.ProbabilityTheory.IndepProduct

namespace Bluebell

open ProbabilityTheory

/-! ## Probability algebra wrappers (skeleton)

We will add lightweight wrappers like `PSp` here without committing to CMRA structure yet. -/

abbrev PSp (Ω : Type*) := WithTop (ProbabilityTheory.ProbabilitySpace Ω)

namespace PSp

-- Placeholder: future helpers for compatibility will go here.

end PSp

variable {Ω : Type*}

noncomputable section

/-- Trivial probability space `{∅, Ω}` with Dirac measure at an arbitrary point (requires `Nonempty Ω`). -/
instance [inst : Nonempty Ω] : One (ProbabilityTheory.ProbabilitySpace Ω) where
  one := @ProbabilityTheory.ProbabilitySpace.mk Ω (@MeasureTheory.MeasureSpace.mk Ω ⊥ (@MeasureTheory.Measure.dirac _ ⊥ (Classical.choice inst)))
    (by constructor; simp [MeasureTheory.Measure.dirac])

end

end Bluebell
