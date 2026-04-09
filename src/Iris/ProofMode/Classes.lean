/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König
-/
import Iris.BI

namespace Iris.ProofMode
open Iris.BI

/-
The two type classes `AsEmpValid1` and `AsEmpValid2` are necessary since type class instance
search is used in both directions in `as_emp_valid_1` and `as_emp_valid_2`. When type class
instance search is supposed to generate `φ` based on `P`, `AsEmpValid1` is used, since `φ` is
declared as an `outParam`. Consequently, if type class instance search is supposed to generate `P`,
`AsEmpValid2` is used.
-/

class AsEmpValid1 (φ : semiOutParam Prop) {PROP : Type _} (P : PROP) [BI PROP] where
  as_emp_valid : φ ↔ ⊢ P

class AsEmpValid2 (φ : Prop) {PROP : outParam (Type _)} (P : outParam PROP) [BI PROP] where
  as_emp_valid : φ ↔ ⊢ P

def AsEmpValid1.to2 {φ : Prop} {PROP : Type _} {P : PROP} [BI PROP]
    [AsEmpValid1 φ P] : AsEmpValid2 φ P := ⟨AsEmpValid1.as_emp_valid⟩

def AsEmpValid2.to1 {φ : Prop} {PROP : Type _} {P : PROP} [BI PROP]
    [AsEmpValid2 φ P] : AsEmpValid1 φ P := ⟨AsEmpValid2.as_emp_valid⟩

theorem as_emp_valid_1 [BI PROP] (P : PROP) [AsEmpValid1 φ P] : φ → ⊢ P :=
  AsEmpValid1.as_emp_valid.mp
theorem as_emp_valid_2 [BI PROP] (φ : Prop) [AsEmpValid2 φ (P : PROP)] : (⊢ P) → φ :=
  AsEmpValid2.as_emp_valid.mpr


/- Depending on the use case, type classes with the prefix `From` or `Into` are used. Type classes
with the prefix `From` are used to generate one or more propositions *from* which the original
proposition can be derived. Type classes with the prefix `Into` are used to generate propositions
*into* which the original proposition can be turned by derivation. Additional boolean flags are
used to indicate that certain propositions should be intuitionistic. -/

class IntoEmpValid (φ : Prop) {PROP : outParam (Type _)} (P : outParam PROP) [BI PROP] where
  into_emp_valid : φ → ⊢ P
export IntoEmpValid (into_emp_valid)

class FromImp [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_imp : (Q1 → Q2) ⊢ P
export FromImp (from_imp)

class FromWand [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_wand : (Q1 -∗ Q2) ⊢ P
export FromWand (from_wand)

class IntoWand [BI PROP] (p q : Bool) (R : PROP) (P Q : outParam PROP) where
  into_wand : □?p R ⊢ □?q P -∗ Q
export IntoWand (into_wand)

class FromForall [BI PROP] (P : PROP) {α : outParam (Sort _)} (Ψ : outParam <| α → PROP) where
  from_forall : (∀ x, Ψ x) ⊢ P
export FromForall (from_forall)

class IntoForall [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_forall : P ⊢ ∀ x, Φ x
export IntoForall (into_forall)

class FromExists [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  from_exists : (∃ x, Φ x) ⊢ P
export FromExists (from_exists)

class IntoExists [BI PROP] (P : PROP) {α : outParam (Sort _)} (Φ : outParam <| α → PROP) where
  into_exists : P ⊢ ∃ x, Φ x
export IntoExists (into_exists)

class FromAnd [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_and : Q1 ∧ Q2 ⊢ P
export FromAnd (from_and)

class IntoAnd (p : Bool) [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_and : □?p P ⊢ □?p (Q1 ∧ Q2)
export IntoAnd (into_and)

class FromSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_sep : Q1 ∗ Q2 ⊢ P
export FromSep (from_sep)

class IntoSep [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_sep : P ⊢ Q1 ∗ Q2
export IntoSep (into_sep)

class FromOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  from_or : Q1 ∨ Q2 ⊢ P
export FromOr (from_or)

class IntoOr [BI PROP] (P : PROP) (Q1 Q2 : outParam PROP) where
  into_or : P ⊢ Q1 ∨ Q2
export IntoOr (into_or)


class IntoPersistently (p : Bool) [BI PROP] (P : PROP) (Q : outParam PROP) where
  into_persistently : <pers>?p P ⊢ <pers> Q
export IntoPersistently (into_persistently)

class FromAffinely [BI PROP] (P : outParam PROP) (Q : PROP) (p : Bool := true) where
  from_affinely : <affine>?p Q ⊢ P
export FromAffinely (from_affinely)

class IntoAbsorbingly [BI PROP] (P : outParam PROP) (Q : PROP) where
  into_absorbingly : P ⊢ <absorb> Q
export IntoAbsorbingly (into_absorbingly)


class FromAssumption (p : Bool) [BI PROP] (P : semiOutParam PROP) (Q : PROP) where
  from_assumption : □?p P ⊢ Q
export FromAssumption (from_assumption)

class IntoPure [BI PROP] (P : PROP) (φ : outParam Prop) where
  into_pure : P ⊢ ⌜φ⌝
export IntoPure (into_pure)

class FromPure [BI PROP] (a : outParam Bool) (P : PROP) (φ : outParam Prop) where
  from_pure : <affine>?a ⌜φ⌝ ⊢ P
export FromPure (from_pure)


/-- `Frame p R P Q` states that we can frame resource `R` when proving `P`,
leaving residual goal `Q`. That is, `□?p R ∗ Q ⊢ P`.
This is the core class driving the `iFrame` tactic. -/
class Frame (p : Bool) [BI PROP] (R P : PROP) (Q : outParam PROP) where
  frame : □?p R ∗ Q ⊢ P
export Frame (frame)

/-- `MaybeFrame p R P Q progress` is like `Frame` but tracks whether actual framing
progress was made. When `progress = false`, the default fallback was used (R was
not actually consumed). This prevents exponential blowup in ∧/∨ decomposition. -/
class MaybeFrame (p : Bool) [BI PROP] (R P : PROP)
    (Q : outParam PROP) (progress : outParam Bool) where
  maybe_frame : □?p R ∗ Q ⊢ P
export MaybeFrame (maybe_frame)

/-- `FromModal φ M sel P Q` states that goal `P` can be turned into modality `M`
applied to `Q` under condition `φ`. Used by `iModIntro`. -/
class FromModal {PROP1 PROP2 : Type _} [BI PROP1] [BI PROP2]
    (φ : outParam Prop) (M : PROP1 → PROP2)
    (sel : semiOutParam PROP1) (P : PROP2) (Q : outParam PROP1) where
  from_modal : φ → M Q ⊢ P
export FromModal (from_modal)

/-- `ElimModal φ p p' P P' Q Q'` states how to eliminate a modality from
hypothesis `□?p P` (producing `□?p' P'`) while transforming goal `Q` to `Q'`.
Used by `iMod`. -/
class ElimModal {PROP : Type _} [BI PROP]
    (φ : outParam Prop) (p : Bool) (p' : outParam Bool)
    (P : PROP) (P' : outParam PROP) (Q : PROP) (Q' : outParam PROP) where
  elim_modal : φ → □?p P ∗ (□?p' P' -∗ Q') ⊢ Q
export ElimModal (elim_modal)

/-- `AddModal P P' Q` states that adding modality `P` transforms goal `Q`
via intermediate `P'`. Used for modality-aware goal transformation. -/
class AddModal [BI PROP] (P P' Q : PROP) where
  add_modal : P ∗ (P' -∗ Q) ⊢ Q
export AddModal (add_modal)

/-- `MakeSep P Q PQ` normalizes `P ∗ Q` to `PQ`, simplifying emp away. -/
class MakeSep [BI PROP] (P Q : PROP) (PQ : outParam PROP) where
  make_sep : P ∗ Q ⊣⊢ PQ
export MakeSep (make_sep)

/-- `MakeAnd P Q PQ` normalizes `P ∧ Q` to `PQ`. -/
class MakeAnd [BI PROP] (P Q : PROP) (PQ : outParam PROP) where
  make_and : P ∧ Q ⊣⊢ PQ
export MakeAnd (make_and)

/-- `MakeOr P Q PQ` normalizes `P ∨ Q` to `PQ`. -/
class MakeOr [BI PROP] (P Q : PROP) (PQ : outParam PROP) where
  make_or : P ∨ Q ⊣⊢ PQ
export MakeOr (make_or)

end Iris.ProofMode
