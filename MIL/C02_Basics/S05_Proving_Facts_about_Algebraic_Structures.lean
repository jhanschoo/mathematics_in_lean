import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

#check inf_le_of_left_le
#check inf_le_of_right_le
#check le_sup_of_le_left
#check le_sup_of_le_right

example (h : x ≤ z) : x ⊓ y ≤ z := le_trans inf_le_left h

example (h : y ≤ z) : x ⊓ y ≤ z := le_trans inf_le_right h

example (h : z ≤ x) : z ≤ x ⊔ y := le_trans h le_sup_left

example (h : z ≤ y) : z ≤ x ⊔ y := le_trans h le_sup_right

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · apply inf_le_of_left_le
      apply inf_le_left
    apply le_inf
    · apply inf_le_of_left_le
      apply inf_le_right
    · apply inf_le_right
  · apply le_inf
    apply le_inf
    · apply inf_le_left
    · apply inf_le_of_right_le
      apply inf_le_left
    · apply inf_le_of_right_le
      apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
  · apply sup_le
    · apply le_sup_right
    · apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    apply sup_le
    · apply le_sup_left
    · apply le_sup_of_le_right
      apply le_sup_left
    · apply le_sup_of_le_right
      apply le_sup_right
  · apply sup_le
    · apply le_sup_of_le_left
      apply le_sup_left
    apply sup_le
    · apply le_sup_of_le_left
      apply le_sup_right
    · apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · apply inf_le_left
  · apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

#check inf_sup_self

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  calc
    a ⊔ b ⊓ c = a ⊔ c ⊓ b := by rw [inf_comm]
    _ = a ⊔ a ⊓ c ⊔ c ⊓ b := by rw [sup_inf_self]
    _ = a ⊔ c ⊓ a ⊔ c ⊓ b := by rw [inf_comm]
    _ = a ⊔ (c ⊓ a ⊔ c ⊓ b) := by rw [sup_assoc]
    _ = a ⊔ c ⊓ (a ⊔ b) := by rw [h]
    _ = a ⊔ (a ⊔ b) ⊓ c := by rw [inf_comm]
    _ = a ⊓ (a ⊔ b) ⊔ (a ⊔ b) ⊓ c := by rw [inf_sup_self]
    _ = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by rw [inf_comm]
    _ = (a ⊔ b) ⊓ (a ⊔ c) := by rw [h]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  calc
    a ⊓ (b ⊔ c) = a ⊓ (c ⊔ b) := by rw [sup_comm]
    _ = a ⊓ (a ⊔ c) ⊓ (c ⊔ b) := by rw [inf_sup_self]
    _ = a ⊓ (c ⊔ a) ⊓ (c ⊔ b) := by rw [sup_comm]
    _ = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := by rw [inf_assoc]
    _ = a ⊓ (c ⊔ a ⊓ b) := by rw [h]
    _ = a ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c) := by rw [sup_inf_self]
    _ = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw [sup_comm]
    _ = a ⊓ b ⊔ a ⊓ c := by rw [h]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [sub_eq_add_neg]
  rw [← add_neg_self a]
  exact add_le_add_right h (-a)

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero b]
  rw [← neg_add_self a]
  nth_rw 1 [← zero_add a]
  rw [← add_assoc]
  rw [← sub_eq_add_neg]
  apply add_le_add_right h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h'' : 0 ≤ b * c + -(a * c) := by
    rw [neg_mul_eq_neg_mul, ← right_distrib]
    apply mul_nonneg _ h'
    rw [add_comm]
    rw [← neg_add_self a]
    exact add_le_add_left h (-a)
  have h''' : 0 + a * c ≤ b * c + -(a * c) + a * c := by
    apply add_le_add_right h''
  rw [zero_add, add_assoc, neg_add_self, add_zero] at h'''
  exact h'''

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y * 2 := by
    rw [mul_two]
    nth_rw 2 [dist_comm x y]
    rw [← dist_self x]
    apply dist_triangle
  apply nonneg_of_mul_nonneg_left h zero_lt_two

end
