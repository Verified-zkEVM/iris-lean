import Iris
import Iris.Algebra.CMRA
import Iris.BI.BIBase
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

class Valid (M : Type*) where
  valid : M → Prop

export Valid (valid)

prefix:50(priority := high) "✓" => Valid.valid

instance {α : Type*} [Valid α] (p : α → Prop) : Valid (Subtype p) where
  valid := fun x => Valid.valid x.1

instance {α β : Type*} [Valid α] [Valid β] : Valid (α × β) where
  valid := fun x => Valid.valid x.1 ∧ Valid.valid x.2

/-- The class of **discrete** cameras, which do not care about step-indexing -/
class DiscreteCMRA (α : Type*) extends CommSemigroup α, Valid α where
  equiv : α → α → Prop
  pcore : α → Option α

  is_equiv : Equivalence equiv

  mul_equiv {x y z} : equiv y z → equiv (x * y) (x * z)
  pcore_equiv {x y cx} : equiv x y → pcore x = some cx → ∃ cy, pcore y = some cy ∧ equiv cx cy

  pcore_left {x cx} : pcore x = some cx → equiv (cx * x) x
  pcore_idem {x cx} : pcore x = some cx → pcore cx = some cx
  pcore_mono' {x y cx} : pcore x = some cx → ∃ cy, pcore (x * y) = some (cx * cy)

  valid_equiv {x y} : equiv x y → valid x → valid y
  valid_mul {x y} : valid (x * y) → valid x

open Iris in
instance DiscreteCMRA.instOFE (α : Type*) [DiscreteCMRA α] : OFE α where
  Equiv := equiv
  Dist := fun _ ↦ equiv
  dist_eqv := by simp [DiscreteCMRA.is_equiv]
  equiv_dist := by simp
  dist_lt := fun h _ ↦ h

open Iris in
/-- A discrete CMRA can be converted to a regular CMRA -/
instance DiscreteCMRA.instCMRA {α : Type*} [DiscreteCMRA α] : CMRA α := {
  pcore := pcore
  op := (·*·)
  ValidN := fun _ x ↦ valid x
  Valid := valid
  op_ne := ⟨fun _ _ _ h ↦ mul_equiv h⟩
  pcore_ne := pcore_equiv
  validN_ne := valid_equiv
  valid_iff_validN := by aesop
  validN_succ := by simp
  assoc := by simp [mul_assoc]
  comm := by simp [mul_comm]
  pcore_op_left := pcore_left
  pcore_idem := by
    intro x cx h
    have h₁ := @pcore_idem α _ x cx h
    aesop
  pcore_op_mono := fun {x cx} h y ↦ by
    rcases @pcore_mono' α _ x y cx h with ⟨cy, h⟩
    use cy
    rw [h]
  validN_op_left := valid_mul
  extend {_ _ y₁ y₂ _ _} := by use y₁, y₂; simpa
}

/-- An ordered unital resource algebra is a type with a multiplication, a one, a preorder `≤`,
  and a validity predicate `✓`, such that:

  - `1` is valid
  - validity is downward closed: `a ≤ b → ✓ b → ✓ a`
  - validity of multiplication cancels on the right: `✓ (a * b) → ✓ a`
  - multiplication on the right is monotone: `a ≤ b → a * c ≤ b * c` -/
class OrderedUnitalResourceAlgebra (M : Type*) extends
    CommMonoid M, Valid M, Preorder M, MulRightMono M where
  valid_one : ✓ (1 : M)
  valid_mono {a b : M} : a ≤ b → ✓ b → ✓ a
  valid_mul {a b : M} : ✓ (a * b) → ✓ a

export OrderedUnitalResourceAlgebra (valid_one valid_mono valid_mul)

attribute [simp] valid_one

namespace OrderedUnitalResourceAlgebra

variable {I M : Type*} [OrderedUnitalResourceAlgebra M]

instance : MulRightMono M := ⟨fun _ _ _ h ↦ mul_left_mono h⟩

/-- Lifting the validity predicate to indexed tuples by requiring all elements to be valid -/
@[simp]
instance [Valid M] : Valid (I → M) where
  valid := fun x => ∀ i, ✓ x i

/-- A resource algebra on `M` is lifted pointwise to a resource algebra on `I → M` -/
instance {I : Type*} : OrderedUnitalResourceAlgebra (I → M) where
  valid_one := by intro i; exact valid_one
  valid_mono := by intro _ _ hab hb i; exact valid_mono (hab i) (hb i)
  valid_mul := by intro _ _ hab i; exact valid_mul (hab i)
  elim := by intro _ _ _ h; exact fun i => mul_left_mono (h i)

/-- Define a `DiscreteCMRA` instance given an `OrderedUnitalResourceAlgebra` instance -/
instance instCMRM : DiscreteCMRA M := {
  equiv a b := a = b
  pcore x := some 1
  is_equiv := by constructor; grind; grind; grind
  mul_equiv := by intro x y z h; grind
  pcore_equiv := by grind
  pcore_left := by intro x cx h; grind
  pcore_idem := by simp_all
  pcore_mono' := by intro x y cx h; use 1; grind
  valid_equiv := by grind
  valid_mul := by
    intro x y
    have := @OrderedUnitalResourceAlgebra.valid_mul M _ x y
    aesop
}

end OrderedUnitalResourceAlgebra

/-! ## Permissions -/

/-- A permission on type `α` is a map from `α` to the non-negative rationals `ℚ≥0`.

We need to have the `Multiplicative` tag in order to specify that multiplication is pointwise
addition, and unit is the constant zero map. -/
@[reducible] def Permission (α : Type*) := Multiplicative (α → ℚ≥0)

variable {α β : Type*}

/-- Permissions form an `OrderedUnitalResourceAlgebra` where `≤` is defined pointwise,
  a resource is valid iff it's below `1` pointwise, and composition is pointwise addition -/
instance : OrderedUnitalResourceAlgebra (Permission α) := {
  valid f := ∀ x : α, f x ≤ 1
  one_mul := by simp
  valid_one := by
    intro x
    have : 0 ≤ 1 := by aesop
    aesop
  valid_mono := by
    intro f g hle hv x
    have : f x ≤ g x := by aesop
    grind
  valid_mul := by
    intro a b hab x
    have : ∀ p q : ℚ≥0, p + q ≤ 1 → p ≤ 1 := by
      intro p q h
      have hpq : p ≤ p + q := by
        exact le_add_of_nonneg_right q.property
      exact hpq.trans h
    aesop
  mul_one := by aesop
}

def OrderedUnitalResourceAlgebra.subalgebra
  {α : Type*} {p : α → Prop} (i : OrderedUnitalResourceAlgebra α)
  (hu : p i.one) (hc : ∀ x y : α, p x → p y → p (i.mul x y))
  : OrderedUnitalResourceAlgebra {x : α // p x} := {
  mul x y := ⟨i.mul x.val y.val, hc x.val y.val x.property y.property⟩
  mul_assoc x y z := by
    have : (x.val * y.val) * z.val = x.val * (y.val * z.val) := by grind
    aesop
  one := ⟨i.one, hu⟩
  one_mul := by
    rintro ⟨x, hx⟩
    have : i.one * x = x := by apply i.one_mul
    aesop
  mul_one := by
    rintro ⟨x, hx⟩
    have : x * i.one = x := by apply i.mul_one
    aesop
  mul_comm := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    have : x * y = y * x := by apply i.mul_comm
    aesop
  elim := by
    intro a b c h
    have := i.elim
    aesop
  valid_one := by apply i.valid_one
  valid_mono := by
    intro a b h
    have := @i.valid_mono a b h
    aesop
  valid_mul := by
    intro a b h
    have := @i.valid_mul a b h
    aesop
}

def OrderedUnitalResourceAlgebra.indexedProduct
  {I : Type} {α : I → Type*}
  (f : (i : I) → OrderedUnitalResourceAlgebra (α i))
  : OrderedUnitalResourceAlgebra ((i : I) → α i) := {
  mul x y i := (f i).mul (x i) (y i)
  mul_assoc x y z := by funext; simp; grind
  one i := (f i).one
  one_mul x := by simp
  mul_one x := by simp
  mul_comm x y := by funext; simp; grind
  valid x := ∀ i : I, valid (x i)
  le x y := ∀ i : I, (f i).le (x i) (y i)
  le_refl x i := by grind
  le_trans x y z h₁ h₂ := by grind
  elim := by intro a b c h i; unfold Function.swap; simp; have := (f i).elim; aesop
  valid_one i := by aesop
  valid_mono x y i := by have := fun i ↦ (f i).valid_mono (x i) (y i); aesop
  valid_mul x := by have := fun i ↦ (f i).valid_mul (x i); aesop
}

/-- Technically binary product is just an instnace of indexed product, but
    it is convenient to redefine it -/
def OrderedUnitalResourceAlgebra.product
  {α β : Type u}
  (r₁ : OrderedUnitalResourceAlgebra α) (r₂ : OrderedUnitalResourceAlgebra β)
  : OrderedUnitalResourceAlgebra (α × β) := {
  elim := by
    intro a b c h
    unfold Function.swap
    simp_all
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    obtain ⟨c₁, c₂⟩ := c
    simp_all
    constructor
    · have := @r₁.elim a₁ b₁ c₁ h.1
      aesop
    · have := @r₂.elim a₂ b₂ c₂ h.2
      aesop
  valid_one := by constructor; aesop; aesop
  valid_mono := by
    intro a b h₁ h₂
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    have : ✓ a₁ := @r₁.valid_mono a₁ b₁ h₁.1 h₂.1
    have : ✓ a₂ := @r₂.valid_mono a₂ b₂ h₁.2 h₂.2
    constructor; aesop; aesop
  valid_mul := by
    intro a b h
    obtain ⟨a₁, a₂⟩ := a
    obtain ⟨b₁, b₂⟩ := b
    simp_all
    have : ✓ a₁ := @r₁.valid_mul a₁ b₁ h.1
    have : ✓ a₂ := @r₂.valid_mul a₂ b₂ h.2
    constructor; aesop; aesop
}
