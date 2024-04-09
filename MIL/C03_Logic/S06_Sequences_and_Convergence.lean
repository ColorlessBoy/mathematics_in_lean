import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _
  rw [sub_self, abs_zero]
  apply εpos

#check le_max_iff
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  rw [add_sub_add_comm]
  have h2 : |s n - a| + |t n - b| < ε := by
    have h3: ε = ε / 2 + ε / 2 := by ring
    rw [h3]
    apply add_lt_add
    apply hs n (le_of_max_le_left hn)
    apply ht n (le_of_max_le_right hn)
  apply lt_of_le_of_lt (abs_add_le _ _) h2

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    repeat
    rw [h, zero_mul]
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε he
  dsimp
  obtain h2:= cs (ε / |c|)
  have h3: ε / |c| > 0 := div_pos he acpos
  obtain ⟨N, hN⟩ := h2 h3
  use N
  intro n hn
  have cne0 : |c| ≠ 0 := by linarith
  rw [← mul_sub, abs_mul, ← div_mul_cancel ε cne0, mul_comm, mul_lt_mul_right]
  exact hN n hn
  apply abs_pos.mpr (abs_ne_zero.mp cne0)

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngeN
  rw [← sub_add_cancel (s n) a, add_comm]
  apply lt_of_le_of_lt (abs_add_le _ _)
  rw [add_lt_add_iff_left]
  exact h n ngeN

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use (max N₀ N₁)
  intro n ngeN0N1
  apply Nat.max_le.mp at ngeN0N1
  have Bne0 : B ≠ 0 := by linarith
  rw [← mul_zero (s n), ← mul_sub, ← div_mul_cancel ε Bne0, mul_comm, abs_mul]
  apply mul_lt_mul' (le_of_lt (h₁ n ngeN0N1.right)) (h₀ n ngeN0N1.left) (abs_nonneg _) pos₀

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    rw [← add_neg_self b]
    apply convergesTo_add ct (convergesTo_const (-b))
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  rw [zero_add, mul_comm]

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := abs_pos.mpr (sub_ne_zero.mpr abne)
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have h1: max Na Nb ≥ Na := le_max_left _ _
    apply hNa N h1
  have absb : |s N - b| < ε := by
    have h1: max Na Nb ≥ Nb := le_max_right _ _
    apply hNb N h1
  have : |a - b| < |a - b| := by
    nth_rw 1 [← sub_add_cancel a (s N), ← add_sub]
    apply lt_of_le_of_lt (abs_add_le _ _)
    rw [abs_sub_comm]
    apply lt_of_lt_of_le (add_lt_add absa absb)
    apply le_of_eq
    ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
