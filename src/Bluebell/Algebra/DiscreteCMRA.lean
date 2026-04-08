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

@[simp]
abbrev carrier [OrderedUnitalResourceAlgebra M] := M

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

namespace OrderedUnitalResourceAlgebra

def subalgebra
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

def indexedProduct
  {I : Type*} {α : I → Type _}
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
def product
  {α β : Type*}
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

@[simp]
def quotientMul
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) →
    R (ra.mul p₁ q₁) (ra.mul p₂ q₂)) (p q : Quotient R)
  : Quotient R :=
  Quotient.lift₂ (f := fun x y ↦ ⟦ra.mul x y⟧) (by
    intro p₁ q₁ p₂ q₂ hp hq
    have := hclo p₁ q₁ p₂ q₂ hp hq
    exact Quot.sound this) p q

@[simp]
def quotientOne
  {α : Type*} {R : Setoid α} (ra : OrderedUnitalResourceAlgebra α)
  : Quotient R := ⟦ra.one⟧

lemma quotientMul_injective
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  {p q r : Quotient R} (h : p.out * q.out = r.out)
  : quotientMul hclo p q = r := by
  have h₁ : quotientMul hclo ⟦p.out⟧ ⟦q.out⟧ = ⟦p.out * q.out⟧ := rfl
  rw [Quotient.out_eq p, Quotient.out_eq q] at h₁
  rw [h₁, h, Quotient.out_eq]

lemma quotientMul_commutes_out_singleton
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  (x y : α)
  : R ((Quot.mk R x).out * (Quot.mk R y).out) ((quotientMul hclo ⟦x⟧ ⟦y⟧).out) := by
  have : R x (Quot.mk (⇑R) x).out := by
    apply Quotient.exact; symm; exact Quotient.out_eq _
  have : R y (Quot.mk (⇑R) y).out := by
    apply Quotient.exact; symm; exact Quotient.out_eq _
  have h₁ := hclo x y (Quot.mk R x).out (Quot.mk R y).out (by assumption) (by assumption)
  have h₂ : R (x * y) (Quot.mk R (x * y)).out := by
    apply Quotient.exact
    symm
    apply Quot.out_eq _
  apply R.symm
  apply R.symm at h₂
  have := R.trans h₂ h₁
  aesop

lemma quotientMul_commutes_out
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  (p q : Quotient R)
  : R (p.out * q.out) ((quotientMul hclo p q).out) := by
  have := @Quot.induction_on₂ α α (r := R) (s := R)
    (δ := fun p q ↦ R (ra.mul p.out q.out) ((quotientMul hclo p q).out))
    (q₁ := p) (q₂ := q) (by
      have := quotientMul_commutes_out_singleton hclo
      aesop)
  have : R (p.out * q.out) (quotientMul hclo p q).out := by aesop
  assumption

def quotient
  {α : Type*} {R : Setoid α} {ra : OrderedUnitalResourceAlgebra α}
  (hclo : (p₁ q₁ p₂ q₂ : α) → (h₁ : R p₁ p₂) → (h₂ : R q₁ q₂) → R (p₁ * q₁) (p₂ * q₂))
  (hvalid : (x x' : α) → R x x' → ra.valid x → ra.valid x')
  (hle : (x x' y y' : α) → x ≤ y → R x x' → R y y' → x' ≤ y')
  : OrderedUnitalResourceAlgebra (Quotient R) := {
  mul := quotientMul hclo
  mul_assoc := by
    intro p q r
    apply Quot.induction_on₃ (δ := fun p q r ↦
      quotientMul hclo (quotientMul hclo p q) r =
        quotientMul hclo p (quotientMul hclo q r)) p
    intro a b c
    have h : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by
      apply ra.mul_assoc a b c
    conv_rhs => simp; rw [← h]
    rfl
  one := quotientOne (R := R) ra
  one_mul := by
    intro p
    simp [OfNat.ofNat]
    apply Quot.induction_on (r := R) (β := fun p ↦ quotientMul hclo ⟦One.one⟧ p = p) p
    intro a
    apply Quot.sound
    have : ra.mul One.one a = a := by
      have := ra.one_mul a
      assumption
    aesop
  mul_one := by
    intro p
    simp [OfNat.ofNat]
    apply Quot.induction_on (r := R) (β := fun p ↦ quotientMul hclo p ⟦One.one⟧ = p) p
    intro a
    apply Quot.sound
    have : ra.mul a One.one = a := by
      have := ra.mul_one a
      assumption
    aesop
  mul_comm := by
    intro p q
    apply Quot.induction_on₂ (δ := fun p q ↦ quotientMul hclo p q = quotientMul hclo q p) p q
    intro a b
    apply Quot.sound
    have : a * b = b * a := ra.mul_comm a b
    simp [HMul.hMul] at this
    rw [this]
  valid x := ∀ x' : α, ⟦x'⟧ = x → ra.valid x'
  le p q := ∀ p' q' : α, ⟦p'⟧ = p → ⟦q'⟧ = q → p' ≤ q'
  le_refl := by
    intro x p q h₁ h₂
    have hx : ⟦x.out⟧ = x := Quotient.out_eq x
    rw [← hx] at h₁ h₂
    apply hle x.out p x.out q (by aesop)
    · have := Quotient.exact h₁
      exact id (Setoid.symm this)
    · have := Quotient.exact h₂
      exact id (Setoid.symm this)
  le_trans := by
    intro a b c hab hbc p' q' h₁ h₂
    have hab' : a.out ≤ b.out := hab a.out b.out (Quotient.out_eq a) (Quotient.out_eq b)
    have hbc' : b.out ≤ c.out := hbc b.out c.out (Quotient.out_eq b) (Quotient.out_eq c)
    have : a.out ≤ c.out := ra.le_trans a.out b.out c.out hab' hbc'
    apply hle a.out p' c.out q' this
    · have : ⟦a.out⟧ = a := Quotient.out_eq a
      rw [← this] at h₁
      apply Quotient.exact (by aesop)
    · have : ⟦c.out⟧ = c := Quotient.out_eq c
      rw [← this] at h₂
      apply Quotient.exact (by aesop)
  elim := by
    simp [Covariant, Function.swap]
    intro m n₁ n₂ h p' q' hp hq
    have helim := @ra.elim m.out n₁.out n₂.out
    simp [Function.swap] at helim
    have : n₁.out ≤ n₂.out := by aesop
    have : n₁.out * m.out ≤ n₂.out * m.out := by aesop
    apply hle (n₁.out * m.out) p' (n₂.out * m.out) q' (by assumption)
    · have h₁ := quotientMul_commutes_out hclo n₁ m
      have h₂ : R (quotientMul hclo n₁ m).out p' := by
        have h₃ : ⟦(quotientMul hclo n₁ m).out⟧ = quotientMul hclo n₁ m :=
          Quotient.out_eq _
        have : Quot.mk R p' = ⟦(quotientMul hclo n₁ m).out⟧ := by
          rw [h₃]
          aesop
        have := Quotient.exact this
        apply Quotient.exact
        aesop
      have h₃ : R (n₁.out * m.out) p' := R.trans h₁ h₂
      assumption
    · have h₁ := quotientMul_commutes_out hclo n₂ m
      have h₂ : R (quotientMul hclo n₂ m).out q' := by
        have h₃ : ⟦(quotientMul hclo n₂ m).out⟧ = quotientMul hclo n₂ m :=
          Quotient.out_eq _
        have : Quot.mk R q' = ⟦(quotientMul hclo n₂ m).out⟧ := by
          rw [h₃]
          aesop
        have := Quotient.exact this
        apply Quotient.exact
        aesop
      have h₃ : R (n₂.out * m.out) q' := R.trans h₁ h₂
      assumption
  valid_one := by
    intro o ho
    simp [OfNat.ofNat, One.one] at ho
    have : R o One.one := Quotient.exact ho
    apply hvalid One.one o (R.symm this)
    exact ra.valid_one
  valid_mono := by
    intro a b h₁ h₂ x hx
    have ha : ⟦a.out⟧ = a := Quotient.out_eq a
    have hb : ⟦b.out⟧ = b := Quotient.out_eq b
    have := ra.valid_mono (a := a.out) (b := b.out)
    have : ra.valid a.out := by
      have : a.out ≤ b.out := h₁ a.out b.out ha hb
      have : ra.valid b.out := h₂ b.out hb
      aesop
    have : R x a.out := by
      rw [← ha] at hx
      exact Quotient.exact (by assumption)
    have := hvalid a.out x (R.symm (by assumption)) (by assumption)
    assumption
  valid_mul := by
    intro a b h x hx
    have ha : ⟦a.out⟧ = a := Quotient.out_eq a
    have := ra.valid_mul (a := a.out) (b := b.out)
    have : ra.valid a.out := by
      have : R (a.out * b.out) (quotientMul hclo a b).out := quotientMul_commutes_out hclo a b
      have : ⟦a.out * b.out⟧ = quotientMul hclo a b := by
        have := Quotient.sound this
        have : ⟦(quotientMul hclo a b).out⟧ = quotientMul hclo a b := Quotient.out_eq _
        aesop
      have := h (a.out * b.out) (by aesop)
      aesop
    rw [← ha] at hx
    have : R x a.out := Quotient.exact (by assumption)
    have := hvalid a.out x (R.symm (by assumption)) (by assumption)
    assumption
}

end OrderedUnitalResourceAlgebra
