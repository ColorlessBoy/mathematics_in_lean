import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check le_antisymm
example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

#check le_trans
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  apply le_min
  apply le_trans (min_le_left (min a b) c) (min_le_left a b)
  apply min_le_min_right
  apply min_le_right
  apply le_min
  apply min_le_min_left
  apply min_le_left
  apply le_trans (min_le_right a (min b c)) (min_le_right b c)

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  apply add_le_add_right
  apply min_le_left
  apply add_le_add_right
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check (sub_add_cancel)
#check add_le_add
example : |a| - |b| ≤ |a - b| := by
  rw [← add_sub_cancel |a - b| |b|]
  nth_rw 1 [← sub_add_cancel a b]
  apply sub_le_sub_right
  apply abs_add

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  apply dvd_mul_of_dvd_right
  apply dvd_mul_right
  rw [pow_two]
  apply dvd_mul_right
  rw [pow_two]
  apply dvd_mul_of_dvd_left h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

#check Nat.gcd_dvd_right
example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  apply Nat.dvd_gcd
  apply Nat.gcd_dvd_right m n
  apply Nat.gcd_dvd_left m n
  apply Nat.dvd_gcd
  apply Nat.gcd_dvd_right n m
  apply Nat.gcd_dvd_left n m
end
