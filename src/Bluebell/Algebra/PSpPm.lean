import Iris
import Bluebell.Algebra.Probability
import Bluebell.Algebra.Permission

namespace Bluebell

open Iris ProbabilityTheory

/-! ## ProbabilitySpace × Permission skeleton

We define a placeholder compatibility predicate and the subtype. No instances yet. -/

variable {α V F : Type*} [UFraction F]

-- Placeholder `Permission` reference lives in `Bluebell.Algebra.Permission`.
-- We only reference the name here to shape the subtype; concrete lemmas later.
/-- Stub compatibility predicate between a probability resource `P : PSp (α → V)`
 and a permission `p : Permission α F`.

 Currently defined as `True` to unblock the refactor; replace with the actual
 splitting condition once the probability semantics are finalized. -/
def compatiblePerm (P : PSp (α → V)) (p : Permission α F) : Prop := True

def PSpPm (α V F : Type*) [UFraction F] :=
  { Pp : PSp (α → V) × Permission α F // compatiblePerm (α := α) (V := V) (F := F) Pp.1 Pp.2 }

namespace PSpPm

variable {α V F : Type*} [UFraction F]

/-- Lift a probability space to a `PSpPm` by pairing with the all-one permission. -/
def liftProb (μ : ProbabilityTheory.ProbabilitySpace (α → V)) : PSpPm α V F :=
  ⟨⟨WithTop.some μ, Permission.one (α := α) (F := F)⟩, trivial⟩

end PSpPm

noncomputable section

namespace PSp

variable {α V : Type*}

/-- Combine two probability spaces using independent product lifted to `PSp`.

 This is a thin wrapper over `ProbabilitySpace.indepProduct` that returns `none`
 when the independent product is not available. -/
def indepMul (x y : PSp (α → V)) : PSp (α → V) :=
  match x, y with
  | WithTop.some x, WithTop.some y =>
      match ProbabilityTheory.ProbabilitySpace.indepProduct x y with
      | some z => WithTop.some z
      | none => none
  | _, _ => none

end PSp

namespace PSpPm

open CMRA

variable {α V F : Type*} [UFraction F]

/-- Pointwise combination on `PSpPm`.

 Uses independent product on the probability component (via `PSp.indepMul`) and
 the CMRA operation on the permission component, done pointwise over `α`. -/
def op (x y : PSpPm α V F) : PSpPm α V F :=
  let P' := PSp.indepMul (α := α) (V := V) x.1.1 y.1.1
  let p' : Permission α F := fun a => x.1.2 a • y.1.2 a
  ⟨⟨P', p'⟩, trivial⟩

end PSpPm

/-- Discrete OFE structure for `PSpPm` (stub). We use Leibniz equality and mark
 this as discrete to simplify the early wiring. -/
@[simp] instance : COFE (PSpPm α V F) := COFE.ofDiscrete _ Eq_Equivalence
instance : OFE.Leibniz (PSpPm α V F) := ⟨(·)⟩
instance : OFE.Discrete (PSpPm α V F) := ⟨congrArg id⟩

/-- Stub `CMRA` instance for `PSpPm` sufficient to enable `own`/`sep` wiring.

 - `pcore = none`
 - `ValidN`/`Valid` are `True`
 - `op` uses `PSpPm.op` (independent product + pointwise permission op)

 TODO: prove associativity/commutativity of `indepProduct` and strengthen validity/core. -/
noncomputable instance : CMRA (PSpPm α V F) where
  pcore _ := none
  op x y := PSpPm.op (α := α) (V := V) (F := F) x y
  ValidN _ _ := True
  Valid _ := True
  op_ne := { ne _ _ _ H := by cases H; rfl }
  pcore_ne {_} := by intro _ h; simp
  validN_ne _ := id
  valid_iff_validN := ⟨fun _ _ => True.intro, fun _ => True.intro⟩
  validN_succ := id
  validN_op_left := id
  assoc := by
    -- TODO: once independent product is associative, replace with the actual proof
    intros; sorry
  comm := by
    -- TODO: once independent product is commutative, replace with the actual proof
    intros; sorry
  pcore_op_left := by intro _ _ h; cases h
  pcore_idem := by intro _ _ h; cases h
  pcore_op_mono := by intro _ _ h _; cases h
  /- TODO: non-trivial `extend` once probability-side op is algebraic. -/
  extend {n x y₁ y₂} _ _ := by
    -- Provide the trivial decomposition witnesses
    refine ⟨y₁, y₂, ?_, ?_, ?_⟩
    · sorry
    · simp
    · simp

/-- Discrete CMRA instance for the stub model. -/
instance : CMRA.Discrete (PSpPm α V F) where
  discrete_0 := id
  discrete_valid := id

end

namespace ProbabilityTheory

namespace ProbabilitySpace

/-- Compatibility on `ProbabilitySpace` delegates to the `PSp` version. -/
def compatiblePerm {α V F : Type*} [UFraction F]
    (P : ProbabilityTheory.ProbabilitySpace (α → V)) (p : Bluebell.Permission α F) : Prop :=
  _root_.Bluebell.compatiblePerm (WithTop.some P) p

end ProbabilitySpace

end ProbabilityTheory

namespace PSp

/-- Compatibility for `PSp` (alias to `compatiblePerm`). -/
def compatiblePerm {α V F : Type*} [UFraction F]
    (P : PSp (α → V)) (p : Permission α F) : Prop :=
  _root_.Bluebell.compatiblePerm P p

end PSp

/-- The main model as indexed tuples of `PSpPm`. -/
abbrev IndexedPSpPm (I α V F : Type*) [UFraction F] := I → PSpPm α V F

namespace IndexedPSpPm

variable {I α V F : Type*} [UFraction F]

/-- Lift an indexed family of probability spaces to indexed `PSpPm`. -/
def liftProb (μ : I → ProbabilityTheory.ProbabilitySpace (α → V)) : IndexedPSpPm I α V F :=
  fun i => PSpPm.liftProb (α := α) (V := V) (F := F) (μ i)

instance : FunLike (IndexedPSpPm I α V F) I (PSpPm α V F) where
coe := fun x => x
coe_injective' := by intro x y h; simp [h]

end IndexedPSpPm

end Bluebell
