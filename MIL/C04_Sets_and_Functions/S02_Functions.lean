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
  ext x
  rfl

#check {s, t}

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, hfx⟩
    · left
      use x
    right
    use x
  rintro (⟨x, xs, hfx⟩ | ⟨x, xt, hfx⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  apply mem_image_of_mem f xs
  -- use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro hsv x xs
    show f x ∈ v
    apply hsv
    use x, xs
  intro hxv y yfs
  rcases yfs with ⟨x, xs, xeq⟩
  rw [← xeq]
  exact hxv xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x hx
  have h2: f x ∈ f '' s := hx
  rcases h2 with ⟨z, zs, zeq⟩
  apply h at zeq
  rw [zeq] at zs
  exact zs

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨z, zs, zeq⟩
  have h: f z ∈ u := zs
  rw [← zeq]
  exact h

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, hx⟩
  rw [← hx] at yu
  use x, yu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, xeq⟩
  use x, (h xs)

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  rintro x hx
  exact h hx

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  rfl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, xsu, xeq⟩
  constructor
  use x, xsu.1
  use x, xsu.2

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x1, x1s, x1eq⟩, ⟨x2, x2s, x2eq⟩⟩
  rw [← x2eq] at x1eq
  apply h at x1eq
  rw [x1eq] at x1s
  use x2, ⟨x1s, x2s⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x1, x1s, x1eq⟩, h2⟩
  use x1
  constructor
  · apply And.intro x1s
    intro x1t
    apply h2
    use x1, x1t, x1eq
  exact x1eq

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  rintro x ⟨xfu, xnfv⟩
  constructor
  · exact xfu
  intro fxv
  apply xnfv fxv

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro ⟨⟨x, xs, xeq⟩, yv⟩
    use x
    rw [← xeq] at yv
    exact ⟨⟨xs, yv⟩, xeq⟩
  rintro ⟨x, ⟨xs, fxv⟩, xeq⟩
  constructor
  use x
  rw [← xeq]
  exact fxv

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, fxu⟩, xeq⟩
  constructor
  · use x, xs, xeq
  rw [← xeq]
  exact fxu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, fxu⟩
  constructor
  use x, xs
  exact fxu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · left
    use x, xs
  right
  exact fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, xeq⟩
    use i, x
  rintro ⟨i, ⟨x, xAi, xeq⟩⟩
  use x
  constructor
  use i
  exact xeq

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y
  simp only [mem_image, mem_iInter]
  rintro ⟨x, ⟨h, xeq⟩⟩ i
  use x, h i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp only [mem_iInter, mem_image]
  rintro h
  rcases h i with ⟨x, _, xeq⟩
  use x
  constructor
  intro i2
  rcases h i2 with ⟨x2, x2Ai, x2eq⟩
  rw [← x2eq] at xeq
  apply injf at xeq
  rw [← xeq] at x2Ai
  exact x2Ai
  exact xeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp only [mem_preimage, mem_iUnion]

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp only [mem_preimage, mem_iInter]

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
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

#check sqrt_inj
example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos h
  rw [← sqrt_inj xpos ypos]
  exact h

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  dsimp
  intro h
  rw [← sqrt_inj, sqrt_sq xpos, sqrt_sq ypos] at h
  exact h
  apply sq_nonneg
  apply sq_nonneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y
  dsimp
  constructor
  · rintro ⟨x, _, xeq⟩
    rw [← xeq]
    apply sqrt_nonneg
  intro ypos
  use y^2
  constructor
  dsimp
  apply sq_nonneg
  apply sqrt_sq ypos

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  simp only [mem_range, mem_setOf]
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    apply sq_nonneg
  intro ypos
  use sqrt y
  apply sq_sqrt ypos
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
  · intro h y
    apply h
    apply inverse_spec
    use y
  intro h x1 x2 h2
  rw [← h x1, ← h x2, h2]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    rcases h y with ⟨x, hx⟩
    apply inverse_spec
    use x
  rintro h y
  have h2: f (inverse f y) = y := h y
  use inverse f y
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
  have h₂ : j ∈ S := by
    dsimp
    exact h₁
  have h₃ : j ∉ S := by
    rw [h] at h₁
    exact h₁
  contradiction

-- COMMENTS: TODO: improve this
end
