import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have h1: 2 ∣ m := by
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h1
  have h2: 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have h3: 2 * k ^ 2 = n ^ 2 := by
    have h : 2 ≠ 0 := by linarith
    apply mul_left_cancel₀ h h2
  have h4: 2 ∣ n := by
    apply even_of_even_sqr
    rw [← h3]
    apply dvd_mul_right
  have : 2 ∣ m.gcd n := by
    rw [Nat.dvd_gcd_iff]
    exact ⟨h1, h4⟩
  have : 2 ∣ 1 := by
    rw [← coprime_mn]
    exact this
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro h
  have : p ∣ m ^ 2 := by
    rw [h]
    apply dvd_mul_right
  have h1: p ∣ m := by
    apply Nat.Prime.dvd_of_dvd_pow prime_p this
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h1
  have h4: p ≥ 2 := Nat.Prime.two_le prime_p
  have : p ≠ 0 := by
    linarith
  have h2: p * k ^ 2 = n ^ 2 := by
    apply mul_left_cancel₀ this
    rw [← h, meq]
    ring
  have : p ∣ n ^ 2 := by
    rw [← h2]
    apply dvd_mul_right
  have h3: p ∣ n := by
    apply Nat.Prime.dvd_of_dvd_pow prime_p this
  have : p ∣ 1  := by
    rw [← coprime_mn, Nat.dvd_gcd_iff]
    exact ⟨h1, h3⟩
  apply Nat.le_of_dvd at this
  linarith
  norm_num

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique
#check Nat.factorization

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    rw [factorization_pow']
  have pnz : p ≠ 0 := by
    have h : p ≥ 2 := Nat.Prime.two_le prime_p
    linarith
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul' pnz nsqr_nez, factorization_pow', Nat.Prime.factorization' prime_p]
    ring
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

#check Nat.dvd_sub'
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} (_ : p.Prime) :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · rw [Nat.factorization_zero]
    dsimp
    apply dvd_zero
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    apply factorization_pow'
  have eq2 : (r.succ * n ^ k).factorization p =
      k * n.factorization p + r.succ.factorization p := by
    rw [factorization_mul' r.succ_ne_zero npow_nz, factorization_pow', add_comm]
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  apply Nat.dvd_sub'
  apply Nat.dvd_mul_right
  apply Nat.dvd_mul_right

#check multiplicity
