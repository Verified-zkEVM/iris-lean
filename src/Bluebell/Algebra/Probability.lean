import Bluebell.ProbabilityTheory.IndepProduct

namespace Bluebell

open ProbabilityTheory

/-! ## Probability algebra wrappers (skeleton)

We will add lightweight wrappers like `PSp` here without committing to CMRA structure yet. -/

abbrev PSp (Ω : Type*) := WithTop (ProbabilityTheory.ProbabilitySpace Ω)

namespace PSp

-- Placeholder: future helpers for compatibility will go here.

end PSp

end Bluebell
