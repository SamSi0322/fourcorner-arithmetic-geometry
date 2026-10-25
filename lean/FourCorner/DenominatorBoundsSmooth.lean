import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace FourCorner

/-- A positive natural number whose prime divisors are all 2 or 3 is a product
of a power of 2 and a power of 3. This is a symbolic factorization argument. -/
theorem two_three_factorization (N : ℕ) (hN : 0 < N)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ N → p = 2 ∨ p = 3) :
    ∃ a b : ℕ, N = 2 ^ a * 3 ^ b := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases h1 : N = 1
    · exact ⟨0, 0, by simpa using h1⟩
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨k, hNk⟩ := hpdvd
    have hk : 0 < k := by
      by_contra! h
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero h
      simp [hk0] at hNk
      omega
    have hklt : k < N := by
      rw [hNk]
      nlinarith [hp.two_le]
    have hksupport : ∀ q : ℕ, q.Prime → q ∣ k → q = 2 ∨ q = 3 := by
      intro q hq hqk
      apply hprime q hq
      rw [hNk]
      exact dvd_mul_of_dvd_right hqk p
    obtain ⟨a, b, hab⟩ := ih k hklt hk hksupport
    rcases hprime p hp ⟨k, hNk⟩ with hp2 | hp3
    · refine ⟨a + 1, b, ?_⟩
      rw [hNk, hp2, hab, pow_succ]
      ring
    · refine ⟨a, b + 1, ?_⟩
      rw [hNk, hp3, hab, pow_succ]
      ring

/-- A positive number which is not 2,3-smooth has a prime divisor at least 5. -/
theorem exists_large_prime_of_not_two_three (N : ℕ) (hN : 0 < N)
    (hnot : ¬ ∃ a b : ℕ, N = 2 ^ a * 3 ^ b) :
    ∃ p : ℕ, p.Prime ∧ p ∣ N ∧ 5 ≤ p := by
  by_contra! h
  apply hnot
  apply two_three_factorization N hN
  intro p hp hpdvd
  have hlt : p < 5 := h p hp hpdvd
  have hp2 : 2 ≤ p := hp.two_le
  interval_cases p <;> norm_num at hp ⊢
  exact Nat.not_prime_mul (by decide : (2 : ℕ) ≠ 1) (by decide : (2 : ℕ) ≠ 1) hp

#print axioms two_three_factorization
#print axioms exists_large_prime_of_not_two_three
end FourCorner
