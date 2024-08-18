import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro fimgsv x xs
    exact fimgsv ⟨x, xs, rfl⟩
  · rintro sfprev x ⟨y, ys, fxy⟩
    rw [← fxy]
    use sfprev ys

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxy⟩
  apply h at fxy
  rwa [← fxy]

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, fxy, rfl⟩
  exact fxy

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro x xu
  rcases h x with ⟨y, rfl⟩
  use y, xu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x ⟨y, ys, fxy⟩
  use y, h ys, fxy

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xfpreu
  exact h xfpreu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · rintro (fpreu | fprev)
    · exact Or.inl fpreu
    · exact Or.inr fprev
  · rintro (fpreu | fprev)
    · exact Or.inl fpreu
    · exact Or.inr fprev

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, fxy⟩
  exact ⟨⟨x, xs, fxy⟩, ⟨x, xt, fxy⟩⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x ⟨⟨y, ys, fxy⟩, ⟨z, zt, fxz⟩⟩
  rw [← fxz] at fxy
  apply h at fxy
  rw [fxy] at ys
  simp
  use z

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, xs, rfl⟩, xt⟩
  simp at *
  by_cases h : x ∈ t
  · have : ¬f x = f x := xt x h
    contradiction
  · use x, ⟨xs, h⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨fpreu, fprenv⟩
  exact ⟨fpreu, fprenv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y; constructor <;> simp
  · rintro x xs rfl fxv
    use x
  · rintro x xs fxv rfl
    exact ⟨⟨x, xs, rfl⟩, fxv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y
  simp
  rintro x xs fxu rfl
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  exact ⟨⟨x, xs, rfl⟩, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · exact Or.inl ⟨x, xs, rfl⟩
  · exact Or.inr fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; constructor <;> simp
  · rintro x i xa rfl
    use i, x
  · rintro i x xa rfl
    use x, ⟨i, xa⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp
  rintro x xai rfl i
  use x, xai i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  rintro h
  rcases h i with ⟨x, _, rfl⟩
  have : ∀ (i : I), x ∈ A i := by
    intro j
    rcases h j with ⟨x', xai', fx'fx⟩
    apply injf at fx'fx
    rw [← fx'fx]
    exact xai'
  use x, this

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x px x' px' heq
  calc
    x = sqrt x * sqrt x := by rw [mul_self_sqrt px]
    _ = sqrt x' * sqrt x' := by rw [heq]
    _ = x' := by rw [mul_self_sqrt px']


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x px x' px' heq
  dsimp at *
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq px]
    _ = sqrt (x' ^ 2) := by rw [heq]
    _ = x' := by rw [sqrt_sq px']

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, _, rfl⟩
    exact sqrt_nonneg x
  · intro ypos
    use y ^ 2
    dsimp at *
    exact ⟨sq_nonneg y, sqrt_sq ypos⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    exact sq_nonneg x
  · intro ypos
    use sqrt y
    dsimp at *
    exact sq_sqrt ypos

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro injf
    intro x
    rw [inverse, dif_pos ⟨x, rfl⟩]
    apply injf
    have : ∃ x', f x' = f x := ⟨x, rfl⟩
    exact Classical.choose_spec this
  · intro linvf x₁ x₂ fx₁fx₂
    rw [← linvf x₁, ← linvf x₂, fx₁fx₂]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro surjf
    intro y
    exact inverse_spec y (surjf y)
  · intro rinvf x
    use (inverse f x)
    exact rinvf x
end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [← h]
  contradiction

-- COMMENTS: TODO: improve this
end
