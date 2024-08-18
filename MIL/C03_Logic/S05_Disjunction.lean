import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 (x + y) with hxy | hxy
  · rw [abs_of_nonneg hx, abs_of_nonneg hxy]
    linarith [le_abs_self y]
  · rw [abs_of_nonneg hx, abs_of_neg hxy]
    have : y < 0 := by linarith
    rw [abs_of_neg this]
    linarith
  · rw [abs_of_neg hx, abs_of_nonneg hxy]
    have : 0 ≤ y := by linarith
    rw [abs_of_nonneg this]
    linarith
  · rw [abs_of_neg hx, abs_of_neg hxy]
    linarith [neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h' | h'
  · rw [abs_of_nonneg h']
    constructor
    · intro h
      left
      exact h
    · rintro (h | h)
      · exact h
      · linarith
  · rw [abs_of_neg h']
    constructor
    · intro h
      right
      exact h
    · rintro (h | h)
      · linarith
      · exact h

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    constructor
    · intro h
      constructor <;> linarith
    · rintro ⟨_, h₂⟩
      exact h₂
  · rw [abs_of_neg hx]
    constructor
    · intro h
      constructor <;> linarith
    · rintro ⟨h₁, _⟩
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x - 1) * (x + 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left; linarith
  · right; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x - y) * (x + y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left; linarith
  · right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : (x + -1) * (x + 1) = 0 := by
    calc
      (x + -1) * (x + 1) = (x + -1) * x + (x + -1) * 1 := by simp [mul_add]
      _ = (x + -1) * x + x + -1 := by rw [mul_one, ← add_assoc]
      _ = x * x + -1 * x + x + -1 := by rw [add_mul]
      _ = x * x + -(1 * x) + x + -1 := by simp
      _ = x * x + -x + x + -1 := by simp
      _ = x * x + (-x + x) + -1 := by simp
      _ = x * x + 0 + -1 := by simp
      _ = x * x + -1 := by simp
      _ = x ^ 2 + -1 := by rw [pow_two]
      _ = 1 + -1 := by rw [h]
      _ = 0 := by simp
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left
    apply add_right_cancel
    rewrite [h]; simp
  · right
    apply add_right_cancel
    rewrite [h]; simp

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : (x + -y) * (x + y) = 0 :=
    calc
      (x + -y) * (x + y) = x ^ 2 + -y ^ 2 := by ring
      _ = 0 := by simp [h]
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left
    apply add_right_cancel
    rewrite [h]; simp
  · right
    apply add_right_cancel
    rewrite [h]; simp

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      exact h'
  · intro h hP
    rcases h with h | h
    · contradiction
    · exact h
