/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Bluebell.Assertion
import Iris.ProofMode

/-! ## Bluebell-specific proof mode instances

Register Bluebell's Assertion connectives with the Iris proof mode
type class system so that tactics like iintro, icases, iapply, iframe,
imodintro work with Bluebell goals.
-/

namespace Bluebell

open Iris.BI Iris.ProofMode

variable {M : Type*} [OrderedUnitalResourceAlgebra M] [OneLe M]

/-! ### Persistent instances -/

-- Pure propositions are persistent (⌜φ⌝ doesn't depend on resources)
instance persistent_pure (φ : Prop) :
    Persistent (PROP := Assertion M) (BIBase.pure φ) where
  persistent := fun _ hP => hP

-- emp is persistent (1 ≤ 1 always holds)
instance persistent_emp : Persistent (PROP := Assertion M) (BIBase.emp) where
  persistent := fun _ _ => le_refl 1

-- <pers> P is persistent (P 1 → P 1)
instance persistent_persistently (P : Assertion M) :
    Persistent (BIBase.persistently P) where
  persistent := fun _ hP => hP

/-! ### FromPure / IntoPure instances -/

-- lift φ ↔ ⌜φ⌝: IntoPure for lift
instance intoPure_lift (φ : Prop) :
    IntoPure (PROP := Assertion M) (BIBase.pure φ) φ where
  into_pure := .rfl

-- FromPure for lift (non-affine version)
instance fromPure_lift (φ : Prop) :
    FromPure (PROP := Assertion M) false (BIBase.pure φ) φ where
  from_pure := .rfl

/-! ### Affine instances -/

-- In Bluebell, ALL propositions are affine (via BIAffine)
-- This is already provided by assertionBIAffine

/-! ### FromAssumption instances -/

-- These come from the generic Iris instances and should work via BIAffine

end Bluebell
