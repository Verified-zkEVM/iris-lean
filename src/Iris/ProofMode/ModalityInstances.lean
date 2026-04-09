/-
Copyright (c) 2025 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
import Iris.BI
import Iris.BI.DerivedLaws
import Iris.ProofMode.Modalities
import Iris.ProofMode.Classes

namespace Iris.ProofMode
open Iris.BI

section Modalities

variable [BI PROP]

instance : IsModal (PROP1 := PROP) persistently (.id rfl) .clear where
  spec_intuitionistic _ := persistent
  spec_spatial P := persistently_absorbing P
  emp := persistently_emp_2
  mono := (persistently_mono ·)
  sep := persistently_sep_2

instance : IsModal (PROP1 := PROP) affinely (.id rfl) (.forall rfl Affine) where
  spec_intuitionistic _ := affinely_intro .rfl
  spec_spatial _ _ := affinely_intro .rfl
  emp := affinely_intro .rfl
  mono := (affinely_mono ·)
  sep := affinely_sep_2

instance : IsModal (PROP1 := PROP) intuitionistically (.id rfl) .isEmpty where
  spec_intuitionistic _ := intuitionistic
  spec_spatial := trivial
  emp := intuitionistic
  mono := (intuitionistically_mono ·)
  sep := intuitionistically_sep_2

/-! ## FromModal instances -/

-- FromModal for persistently: goal <pers> P becomes P
instance fromModal_persistently : FromModal (PROP1 := PROP) (PROP2 := PROP)
    True persistently iprop(emp) iprop(<pers> P) P where
  from_modal _ := .rfl

-- FromModal for affinely: goal <affine> P becomes P
instance fromModal_affinely : FromModal (PROP1 := PROP) (PROP2 := PROP)
    True affinely iprop(emp) iprop(<affine> P) P where
  from_modal _ := .rfl

-- FromModal for intuitionistically: goal □ P becomes P
instance fromModal_intuitionistically : FromModal (PROP1 := PROP) (PROP2 := PROP)
    True intuitionistically iprop(emp) iprop(□ P) P where
  from_modal _ := .rfl

-- FromModal for identity: any goal P becomes P (lowest priority)
instance (priority := default - 100) fromModal_id : FromModal (PROP1 := PROP) (PROP2 := PROP)
    True id iprop(emp) P P where
  from_modal _ := .rfl

end Modalities
