import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  apply lt_of_le_of_lt (pow_two_nonneg x) h

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

#check le_of_lt
theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, le_neg_self_iff]
    exact le_of_lt h

#check abs_of_nonneg
theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, neg_le_self_iff]
    exact h
  · rw [abs_of_neg h]

#check neg_add
theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with hxy | hxy
  · rw [abs_of_nonneg hxy]
    apply add_le_add (le_abs_self x) (le_abs_self y)
  · rw [abs_of_neg hxy, neg_add]
    apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact Or.inl
  · rw [abs_of_neg hy]
    exact Or.inr
  intro h
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    rcases h with h1 | h1
    exact h1
    exact lt_of_lt_of_le h1 (neg_le_self hy)
  · rw [abs_of_neg hy]
    rcases h with h1 | h1
    exact lt_trans h1 (lt_neg_self_iff.mpr hy)
    exact h1

#check neg_lt
#check neg_lt
theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    intro h1
    constructor
    apply lt_of_lt_of_le _ hx
    rw [neg_lt, neg_zero]
    apply lt_of_le_of_lt hx h1
    exact h1
  · rw [abs_of_neg hx]
    intro h1
    constructor
    rw [neg_lt]
    exact h1
    apply lt_trans hx (lt_trans _ h1)
    rw [lt_neg, neg_zero]
    exact hx
  intro ⟨h1, h2⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact h2
  · rw [abs_of_neg hx, neg_lt]
    exact h1
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
  rcases h with ⟨x, y, hxy | hxy⟩
  rw [hxy, ← add_zero 0]
  apply add_le_add (pow_two_nonneg x) (pow_two_nonneg y)
  rw [hxy, ← add_zero 0]
  apply add_le_add
  rw [← add_zero 0]
  apply add_le_add (pow_two_nonneg x) (pow_two_nonneg y)
  norm_num

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x - 1) * (x + 1) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2 | h2
  left
  linarith
  right
  linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1: (x - y) * (x + y) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2 | h2
  left
  linarith
  right
  linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

#check eq_zero_or_eq_zero_of_mul_eq_zero
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : (x + 1) * (x - 1) = 0 := by
    rw [← pow_two_sub_pow_two, one_pow, sub_eq_zero]
    exact h
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2 | h2
  right
  rw [← sub_neg_eq_add, sub_eq_zero] at h2
  exact h2
  left
  apply sub_eq_zero.mp h2

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1 : (x + y) * (x - y) = 0 := by
    rw [← pow_two_sub_pow_two, sub_eq_zero]
    exact h
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2 | h2
  right
  rw [← sub_neg_eq_add, sub_eq_zero] at h2
  exact h2
  left
  apply sub_eq_zero.mp h2
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
  · intro h1
    by_cases h2 : P
    exact Or.inr (h1 h2)
    exact Or.inl h2
  intro h1
  rcases h1 with h2 | h2
  intro h3
  contradiction
  intro _
  exact h2
