import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true


class One₁ (α : Type) where
  /-- The element one -/
  one : α


-- instance synthesis: when declared with the class keyword, we are able to talk about One₁ generically as though it has an instance synthesized for it,
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

-- Observe the different signature: we need to explicitly pass the instance as an argument here
#check One₂.one

-- Look at mathlib's One.one : ℕ, which already has an instance defined for it
#check (One.one : ℕ)

-- We cannot currently do the same for One₁.one
-- #check (One₁.one : ℕ)

-- These examples are bogus, because we cannot synthesize an instance for One₁ ℕ (yet)
example (α : Type) [One₁ α] : α := One₁.one

example (α : Type) [One₁ α] := (One₁.one : α)

-- Annotation specifies that documentation for One₁.one should be shown in uses of the symbol 𝟙
@[inherit_doc]
notation "𝟙" => One₁.one -- Defining the notation itself

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl


class Dia₁ (α : Type) where
  dia : α → α → α

-- Defining the notation itself, alongside l/r-associativity and precedence
infixl:70 " ⋄ "   => Dia₁.dia

-- Manually specifying that Semigroup₁ is a specialization of Dia₁ (at this point, toDia₁ has no special treatment)
class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

-- We now tell Lean that toDia₁ can be used when we use a Semigroup₁ where a Dia₁ is expected
attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

-- Better syntax for the above
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α

-- note that this gives two distinct instances for Dia₁ α, one from Semigroup₁ and one from DiaOneClass₁
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α

-- the automatic version chooses one and aliases it to the other
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

-- We see that lean has torn the DiaOneClass₁ instance apart and will separately synthesize the DiaOneClass₁ instance
-- then, Monoid₁.toDiaOneClass₁ is not a field, and we see that we have to have special handling in to_additive later
/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁


class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]

-- Export particular fields of classes to the top level
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)


example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
  left_inv_eq_right_inv₁ (inv_dia a) h

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have h : (a ⋄ a⁻¹)⁻¹ ⋄ (a ⋄ a⁻¹ ⋄ (a ⋄ a⁻¹)) = 𝟙 := by
    rw [dia_assoc, ← dia_assoc a⁻¹ a, inv_dia, one_dia, inv_dia]
  rw [← h, ← dia_assoc, inv_dia, one_dia]




class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

-- tells lean that AddSemigroup₃ is the additive analog of Semigroup₃
@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

-- tells lean that AddMonoid₃ is the additive analog of Monoid₃
@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

-- as mentioned previously, toMulOneClass is not a field of Monoid₃ and so requires special handling
attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

-- @[to_additive] tells lean that to generate the additive analog of the following lemma
whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1

-- registering the fields with the simplifier
attribute [simp] Group₃.inv_mul AddGroup₃.neg_add



@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  rw [← mul_one a⁻¹, ← h, ← mul_assoc₃, Group₃.inv_mul, one_mul]

-- registering the the additive analog's version of the lemma with the simplifier (this also registers the lemma itself with the simplifier)
@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc₃ a a⁻¹ (a * a⁻¹), ← mul_assoc₃ a⁻¹ a, inv_mul, one_mul, inv_mul]
  rw [← h, ← mul_assoc₃, inv_mul, one_mul]

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← one_mul c, ← Group₃.inv_mul a, mul_assoc₃, mul_assoc₃, h]

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  rw [← mul_one b, ← mul_one c, ← Group₃.mul_inv, ← mul_assoc₃, h, mul_assoc₃]

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G



class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have h₁ : (1 + 1) * (a + b) = a + (a + b + b) := by
      rw [Ring₃.left_distrib]
      repeat rw [Ring₃.right_distrib]
      repeat rw [one_mul]
      repeat rw [← add_assoc₃]
    have h₂ : (1 + 1) * (a + b) = a + (b + a + b) := by
      rw [Ring₃.right_distrib, one_mul]
      repeat rw [add_assoc₃]
    apply add_right_cancel₃
    apply add_left_cancel₃
    rw [← h₁, h₂]
   }

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type) extends LE₁ α where
  le_refl₁ : ∀ a : α, a ≤₁ a
  le_trans₁ {a b c : α} : a ≤₁ b → b ≤₁ c → a ≤₁ c

class PartialOrder₁ (α : Type) extends Preorder₁ α where
  le_antisymm₁ {a b : α} : a ≤₁ b → b ≤₁ a → a = b

class OrderedCommMonoid₁ (α : Type) extends CommMonoid₃ α, PartialOrder₁ α where
  mul_le_mul_left₁ {a b : α} : ∀ c : α, a ≤₁ b → c * a ≤₁ c * b

instance : OrderedCommMonoid₁ ℕ where
  mul_assoc₃ := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  le := (· ≤ ·)
  le_refl₁ := Nat.le_refl
  le_trans₁ := Nat.le_trans
  le_antisymm₁ := Nat.le_antisymm
  mul_le_mul_left₁ := Nat.mul_le_mul_left

class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul

-- each class appearing in the extends clause should mention every type appearing in the parameters of the class
-- otherwise, specify them as a parameter in square brackets
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

-- observe that we have added data here as smul, and yet selfModule is not concrete
--   (recall in comparison where we added data elsewhere,
--   in SMul, in LE, One, Dia; all at the top of their hierarchies. This will come to bite us later)
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

-- observe that we have added data here as smul, and yet abGrpModule is not concrete
--   (recall in comparison where we added data elsewhere,
--   in SMul, in LE, One, Dia; all at the top of their hierarchies. This will come to bite us later)
instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry

-- demonstration that the synthesized instance is bad
-- the robust way to fix the diamond problem is to ensure that going from rich structure to poor structure
-- we always forget data, not define data. We call this "forgetful inheritance" (https://inria.hal.science/hal-02463336)
-- see: library_note "forgetful inheritance" in https://github.com/leanprover-community/mathlib4/Mathlib/Algebra/Group/Defs.lean
#synth Module₁ ℤ ℤ -- abGrpModule ℤ
-- and not selfModule ℤ
-- these two concrete instances are not definitionally equal, though they actually are

-- to fix thes particular case, we consider defining a default notion of nsmul way higher in the hierarchy
-- Here, we can modify the definition of AddMonoid₃ to include a nsmul data field and some Prop-valued fields ensuring this operation is provably the one we constructed above.
-- This is the more natural place to establish the relationship between monoids and ℕ (analogous to groups and ℤ)
class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

-- we demonstrate how this works with the product monoid
-- and observe that we did not need to define the fields that have default values in AddMonoid₄
instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

-- we now show that ℤ is a monoid
-- we see we have replaced the definition of nsmul with the one we want
-- but of course, while it has different computational and definitional properties, the mathematical relationship is the same
instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

-- we now show that it is possible to provide a scalar multiplication for ℕ → ℤ → ℤ
example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl

-- This story then continues with incorporating a zsmul field into the definition of groups and similar tricks.

class LT₁ (α : Type) where
  /-- The Less-Than relation. -/
  lt : α → α → Prop

@[inherit_doc] infix:50 " <₁ " => LT₁.lt

class Preorder₂ (α : Type) extends LE₁ α, LT₁ α where
  le_refl₁ : ∀ a : α, a ≤₁ a
  le_trans₁ {a b c : α} : a ≤₁ b → b ≤₁ c → a ≤₁ c
  lt := fun a b ↦ a ≤₁ b ∧ ¬b ≤₁ a
  lt_iff_le_not_le : ∀ a b : α, a <₁ b ↔ a ≤₁ b ∧ ¬ b ≤₁ a := by intros; rfl
