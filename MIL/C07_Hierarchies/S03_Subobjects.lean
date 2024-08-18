import MIL.Common
import Mathlib.GroupTheory.QuotientGroup

set_option autoImplicit true

-- recall that Set α is the type of functions from α to Prop
-- To support the notion of subobjects (e.g. subgroups of groups),
-- recall FunLike for morphisms establishing their relationship against the set function
-- similarly, SetLike establishes the relationship between a subobjoct and its carrier set

-- we give an example of what we need to bundle a submonoid
@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' := Submonoid₁.ext


-- the above definition allows us to show that 1 is in any submonoid without having to appeal to the carrier definition directly
example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem
-- We can also talk about N as though it were of type Set M
example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N

-- We also have a coercion from (N : Submonoid₁ M) to (N : Type), (hence we can write (x : N))
-- Check the tooltip documentation for the .property in the below example
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property

-- we now show that a submonoid is a monoid in its own right
-- SetCoe.ext tells us that the coercion from N to M is injective, allowing us to reuse equality lemmas of M in N
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

-- TODO: an analogous development for subgroups

example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P

-- If N ≤ M, then N partitions M; the Setoid M instance here is M furnished with this partition
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := @fun a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩ ↦
      ⟨w*w', N.mul_mem hw hw', z'*z, N.mul_mem hz' hz, by rw [← mul_assoc, ← mul_assoc, h, ← h', mul_assoc, mul_assoc, mul_comm w']⟩
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      rintro x₁ x₂ ⟨x₁', x₁'N, x₂', x₂'N, hx⟩ y₁ y₂ ⟨y₁', y₁'N, y₂', y₂'N, hy⟩
      use x₁'*y₁', N.mul_mem x₁'N y₁'N, x₂'*y₂', N.mul_mem x₂'N y₂'N
      dsimp
      rw [← mul_assoc, ← mul_assoc, mul_assoc x₁, mul_assoc x₂, mul_comm y₁, mul_comm y₂, ← mul_assoc, ← mul_assoc, mul_assoc, hx, hy, ← mul_assoc]
        )
  mul_assoc := by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
      apply Quotient.sound
      dsimp
      rw [mul_assoc]
      apply @Setoid.refl M N.Setoid
  one := QuotientMonoid.mk N 1
  one_mul := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp
      rw [one_mul]
      apply @Setoid.refl M N.Setoid
  mul_one := by
      rintro ⟨a⟩
      apply Quotient.sound
      dsimp
      rw [mul_one]
      apply @Setoid.refl M N.Setoid
