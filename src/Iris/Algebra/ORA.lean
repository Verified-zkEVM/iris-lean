/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ordered Resource Algebra support, ported from MoSel (Rocq)
-/
import Iris.Algebra.OFE

namespace Iris
open OFE

/-!
# Ordered Resource Algebra (ORA)

An Ordered Resource Algebra is like a CMRA but with a custom ordering `≼ₒ` (and its
step-indexed variant `≼ₒ{n}`) instead of the structural inclusion ordering.

The custom ordering need not be reflexive on the whole type (it quantifies over `A`,
not `option A`). This preserves the property: `x ≼ₒ y ↔ x.1 ≼ₒ y.1 ∧ x.2 ≼ₒ y.2`.
-/

/-- An element `x` is **increasing** if composing with `x` on the left
makes things larger in the custom ordering: `∀ y, y ≼ₒ x • y`. -/
class Increasing (op : α → α → α) (OraOrderN : Nat → α → α → Prop) (x : α) : Prop where
  increasing : ∀ n y, OraOrderN n y (op x y)

class ORA (α : Type _) extends OFE α where
  pcore : α → Option α
  op : α → α → α
  ValidN : Nat → α → Prop
  Valid : α → Prop
  /-- The custom ordering on `α`. -/
  OraOrder : α → α → Prop
  /-- The step-indexed custom ordering on `α`. -/
  OraOrderN : Nat → α → α → Prop

  -- Setoid axioms
  op_ne : NonExpansive (op x)
  pcore_ne : x ≡{n}≡ y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ cx ≡{n}≡ cy
  validN_ne : x ≡{n}≡ y → ValidN n x → ValidN n y

  -- Core produces increasing elements
  pcore_increasing : pcore x = some cx →
    Increasing op OraOrderN cx
  -- Increasing is upward-closed in the custom order
  increasing_closed : Increasing op OraOrderN x → OraOrderN n x y →
    Increasing op OraOrderN y

  -- Validity
  valid_iff_validN : Valid x ↔ ∀ n, ValidN n x
  validN_succ : ValidN n.succ x → ValidN n x

  -- Monoid
  assoc : op x (op y z) ≡ op (op x y) z
  comm : op x y ≡ op y x

  -- Core
  pcore_op_left : pcore x = some cx → op cx x ≡ x
  pcore_idem : pcore x = some cx → pcore cx ≡ some cx
  pcore_monoN : OraOrderN n x y → pcore x = some cx →
    ∃ cy, pcore y = some cy ∧ OraOrderN n cx cy

  -- Validity interacts with op
  validN_op_left : ValidN n (op x y) → ValidN n x

  -- Extension axioms (using custom order instead of equality)
  ora_op_extend : ValidN n x → OraOrderN n (op y₁ y₂) x →
    ∃ z₁ z₂, OraOrderN n.succ (op z₁ z₂) x ∧ z₁ ≡{n}≡ y₁ ∧ z₂ ≡{n}≡ y₂
  ora_extend : ValidN n x → OraOrderN n y x →
    ∃ z, OraOrderN n.succ z x ∧ z ≡{n}≡ y

  -- Order axioms
  dist_orderN : x ≡{n}≡ y → OraOrderN n x y
  orderN_S : OraOrderN n.succ x y → OraOrderN n x y
  orderN_trans : OraOrderN n x y → OraOrderN n y z → OraOrderN n x z
  orderN_op : OraOrderN n x x' → OraOrderN n (op x y) (op x' y)
  validN_orderN : ValidN n x → OraOrderN n y x → ValidN n y
  order_orderN : OraOrder x y ↔ ∀ n, OraOrderN n x y

  -- Core is monotone wrt op in the custom order
  pcore_order_op : pcore x ≡ some cx →
    ∃ cxy, pcore (op x y) ≡ some cxy ∧ OraOrder cx cxy

namespace ORA
variable [ORA α]

infix:60 " • " => op

/-- The structural inclusion ordering (defined via op, as in CMRA). -/
def Included (x y : α) : Prop := ∃ z, y ≡ x • z
infix:50 " ≼ " => Included

def IncludedN (n : Nat) (x y : α) : Prop := ∃ z, y ≡{n}≡ x • z
notation:50 x " ≼{" n "} " y:51 => IncludedN n x y

/-- The custom ORA ordering. -/
scoped notation:50 x " ≼ₒ " y:51 => OraOrder x y
/-- The step-indexed custom ORA ordering. -/
scoped notation:50 x " ≼ₒ{" n "} " y:51 => OraOrderN n x y

def op? [ORA α] (x : α) : Option α → α
  | some y => x • y
  | none => x
infix:60 " •? " => op?

prefix:50 "✓ " => Valid
notation:50 "✓{" n "} " x:51 => ValidN n x

class CoreId (x : α) where
  core_id : pcore x ≡ some x
export CoreId (core_id)

class Exclusive (x : α) where
  exclusive0_l y : ¬✓{0} x • y
export Exclusive (exclusive0_l)

class Cancelable (x : α) where
  cancelableN : ✓{n} x • y → x • y ≡{n}≡ x • z → y ≡{n}≡ z
export Cancelable (cancelableN)

class IdFree (x : α) where
  id_free0_r y : ✓{0} x → ¬x • y ≡{0}≡ x
export IdFree (id_free0_r)

class IsTotal (α : Type _) [ORA α] where
  total (x : α) : ∃ cx, pcore x = some cx
export IsTotal (total)

def core (x : α) := (pcore x).getD x

class Discrete (α : Type _) [ORA α] extends OFE.Discrete α where
  discrete_valid {x : α} : ✓{0} x → ✓ x
  discrete_order {x y : α} : x ≼ₒ{0} y → x ≼ₒ y
export Discrete (discrete_valid discrete_order)

end ORA

/-- Unital Ordered Resource Algebra -/
class UORA (α : Type _) extends ORA α where
  unit : α
  unit_valid : ✓ unit
  unit_left_id : unit • x ≡ x
  pcore_unit : pcore unit ≡ some unit

namespace ORA
variable [ORA α]

/-! ## Op -/

theorem op_right_eqv (x : α) {y z : α} (e : y ≡ z) : x • y ≡ x • z := op_ne.eqv e
theorem _root_.Iris.OFE.Equiv.ora_op_r {x y z : α} : y ≡ z → x • y ≡ x • z := op_right_eqv _

theorem op_right_dist (x : α) {y z : α} (e : y ≡{n}≡ z) : x • y ≡{n}≡ x • z :=
  op_ne.ne e
theorem _root_.Iris.OFE.Dist.ora_op_r {x y z : α} : y ≡{n}≡ z → x • y ≡{n}≡ x • z :=
  op_right_dist _

theorem op_commN {x y : α} : x • y ≡{n}≡ y • x := equiv_dist.mp comm n

theorem op_assocN {x y z : α} : x • (y • z) ≡{n}≡ (x • y) • z := equiv_dist.mp assoc n

theorem op_left_eqv {x y : α} (z : α) (e : x ≡ y) : x • z ≡ y • z :=
  comm.trans <| e.ora_op_r.trans comm
theorem _root_.Iris.OFE.Equiv.ora_op_l {x y z : α} : x ≡ y → x • z ≡ y • z := op_left_eqv _

theorem op_left_dist {x y : α} (z : α) (e : x ≡{n}≡ y) : x • z ≡{n}≡ y • z :=
  op_commN.trans <| e.ora_op_r.trans op_commN
theorem _root_.Iris.OFE.Dist.ora_op_l {x y z : α} : x ≡{n}≡ y → x • z ≡{n}≡ y • z :=
  op_left_dist _

theorem op_right_comm {x y z : α} : x • (y • z) ≡ y • (x • z) := calc
  x • (y • z) ≡ (x • y) • z := assoc
  _           ≡ (y • x) • z := comm.ora_op_l
  _           ≡ y • (x • z) := assoc.symm

/-! ## Validity -/

theorem Valid.validN : ✓ (x : α) → ✓{n} x := (valid_iff_validN.1 · _)

theorem validN_of_eqv {x y : α} : x ≡ y → ✓{n} x → ✓{n} y :=
  fun e v => validN_ne (equiv_dist.mp e n) v

theorem valid_of_eqv {x y : α} : x ≡ y → ✓ x → ✓ y :=
  fun e v => valid_iff_validN.mpr fun n => validN_of_eqv e v.validN

theorem validN_of_le {n n'} {x : α} : n' ≤ n → ✓{n} x → ✓{n'} x :=
  fun le => le.recOn id fun _ ih vs => ih (validN_succ vs)

theorem validN_op_right {n} {x y : α} : ✓{n} (x • y) → ✓{n} y :=
  fun v => validN_op_left (validN_of_eqv comm v)

theorem valid_op_left {x y : α} : ✓ (x • y) → ✓ x :=
  fun v => valid_iff_validN.mpr fun n => validN_op_left v.validN

/-! ## Custom Order -/

theorem orderN_of_le {n n'} {x y : α} (h : x ≼ₒ{n} y) (l : n' ≤ n) : x ≼ₒ{n'} y := by
  induction l with
  | refl => exact h
  | step _ ih => exact ih (orderN_S h)

theorem order_trans {x y z : α} (h1 : x ≼ₒ y) (h2 : y ≼ₒ z) : x ≼ₒ z :=
  order_orderN.mpr fun n => orderN_trans (order_orderN.mp h1 n) (order_orderN.mp h2 n)

instance : Trans (OraOrder : α → α → Prop) OraOrder OraOrder where
  trans := order_trans

instance {n : Nat} : Trans (OraOrderN n : α → α → Prop) (OraOrderN n) (OraOrderN n) where
  trans := orderN_trans

theorem orderN_op_right {n} {x x' : α} (y : α) (h : x ≼ₒ{n} x') : y • x ≼ₒ{n} y • x' := by
  have h1 : x • y ≼ₒ{n} x' • y := orderN_op h
  have h2 : y • x ≼ₒ{n} x • y := dist_orderN op_commN
  have h3 : x' • y ≼ₒ{n} y • x' := dist_orderN op_commN
  exact orderN_trans h2 (orderN_trans h1 h3)

theorem order_op {x x' : α} (y : α) (h : x ≼ₒ x') : x • y ≼ₒ x' • y :=
  order_orderN.mpr fun n => orderN_op (order_orderN.mp h n)

theorem validN_of_orderN {n} {x y : α} : ✓{n} x → y ≼ₒ{n} x → ✓{n} y :=
  validN_orderN

/-! ## Core -/

theorem pcore_proper {x y : α} (cx : α) (e : x ≡ y) (ps : pcore x = some cx)
    : ∃ cy, pcore y = some cy ∧ cx ≡ cy := by
  let ⟨cy, hcy, ecy⟩ := pcore_ne (equiv_dist.mp e 0) ps
  refine ⟨cy, hcy, ?_⟩
  have (n : Nat) : cx ≡{n}≡ cy :=
    let ⟨cy', hcy', ecy'⟩ := pcore_ne (equiv_dist.mp e n) ps
    have : cy' = cy := Option.some_inj.mp (hcy' ▸ hcy)
    this ▸ ecy'
  exact equiv_dist.mpr this

instance : NonExpansive (pcore (α := α)) where
  ne n x {y} e := by
    suffices ∀ ox oy, pcore x = ox → pcore y = oy → pcore x ≡{n}≡ pcore y from
      this (pcore x) (pcore y) rfl rfl
    intro ox oy ex ey
    match ox, oy with
    | .some a, .some b =>
      let ⟨w, hw, ew⟩ := pcore_ne e ex
      calc
        pcore x ≡{n}≡ some a  := .of_eq ex
        _       ≡{n}≡ some w  := ew
        _       ≡{n}≡ pcore y := .of_eq hw.symm
    | .some a, .none =>
      let ⟨w, hw, _⟩ := pcore_ne e ex
      cases hw.symm ▸ ey
    | .none, .some b =>
      let ⟨w, hw, _⟩ := pcore_ne e.symm ey
      cases hw.symm ▸ ex
    | .none, .none => rw [ex, ey]

theorem pcore_op_left' {x : α} {cx} (e : pcore x ≡ some cx) : cx • x ≡ x :=
  let ⟨z, pz, ez⟩ := equiv_some e
  calc
    cx • x ≡ z • x := op_left_eqv _ ez.symm
    _      ≡ x     := pcore_op_left pz

theorem pcore_op_right {x : α} {cx} (e : pcore x = some cx) : x • cx ≡ x :=
  calc
    x • cx ≡ cx • x := comm
    _      ≡ x      := pcore_op_left e

theorem pcore_idem' {x : α} {cx} (e : pcore x ≡ some cx) : pcore cx ≡ some cx :=
  let ⟨y, py, (ey : y ≡ cx)⟩ := equiv_some e
  calc
    pcore cx ≡ pcore y := NonExpansive.eqv ey.symm
    _        ≡ some y  := pcore_idem py
    _        ≡ some cx := ey

theorem pcore_op_right' {x : α} {cx} (e : pcore x ≡ some cx) : x • cx ≡ x :=
  let ⟨_, pz, ez⟩ := equiv_some e
  (op_right_eqv x ez).symm.trans (pcore_op_right pz)

theorem pcore_op_self {x : α} {cx} (e : pcore x = some cx) : cx • cx ≡ cx :=
  pcore_op_right' (pcore_idem e)

theorem pcore_validN {n} {x : α} {cx} (e : pcore x = some cx) (v : ✓{n} x) : ✓{n} cx :=
  validN_op_right (validN_of_eqv (pcore_op_right e).symm v)

/-! ## Structural inclusion -/

theorem inc_op_left (x y : α) : x ≼ x • y := ⟨y, Equiv.rfl⟩
theorem inc_op_right (x y : α) : y ≼ x • y := ⟨x, comm⟩
theorem incN_op_left (n) (x y : α) : x ≼{n} x • y := ⟨y, Dist.rfl⟩

theorem inc_trans {x y z : α} : x ≼ y → y ≼ z → x ≼ z
  | ⟨w, hw⟩, ⟨t, ht⟩ =>
    suffices h : z ≡ x • (w • t) from ⟨w • t, h⟩
    calc
      z ≡ y • t := ht
      _ ≡ (x • w) • t := op_left_eqv _ hw
      _ ≡ x • (w • t) := assoc.symm

instance : Trans (Included (α := α)) Included Included where
  trans := inc_trans

theorem valid_of_inc {x y : α} : x ≼ y → ✓ y → ✓ x
  | ⟨_, hz⟩, v => valid_op_left (valid_of_eqv hz v)

theorem validN_of_incN {n} {x y : α} : x ≼{n} y → ✓{n} y → ✓{n} x
  | ⟨_, hz⟩, v => validN_op_left (validN_ne hz v)

/-! ## Increasing -/

theorem increasing_of_pcore {x cx : α} (h : pcore x = some cx) :
    Increasing op OraOrderN cx :=
  pcore_increasing h

end ORA

namespace UORA
variable [UORA α]

export ORA (op op? Valid ValidN Included IncludedN OraOrder OraOrderN)

open ORA

theorem unit_right_id {x : α} : x • unit ≡ x :=
  comm.trans unit_left_id

theorem unit_valid' : ✓{n} (unit : α) := unit_valid.validN

/-! In a UORA, `≡{n}≡` implies `≼ₒ{n}` (via dist_orderN), and `≡{n}≡` implies `≼{n}`. -/

theorem dist_to_incN {n} {x y : α} (H : x ≡{n}≡ y) : x ≼{n} y :=
  ⟨unit, ((equiv_dist.mp unit_right_id n).trans H).symm⟩

theorem dist_to_orderN {n} {x y : α} (H : x ≡{n}≡ y) : x ≼ₒ{n} y :=
  dist_orderN H

end UORA

end Iris
