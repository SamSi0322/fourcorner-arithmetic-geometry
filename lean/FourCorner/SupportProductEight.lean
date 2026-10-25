import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

namespace FourCorner

/-- If every prime divisor of a nonzero natural number is congruent to
`1` or `7` modulo `8`, the number itself is congruent to `1` or `7`. -/
theorem nat_mod_eight_of_prime_divisors (n : ℕ) (hn : n ≠ 0)
    (hs : ∀ p : ℕ, p.Prime → p ∣ n → p % 8 = 1 ∨ p % 8 = 7) :
    n % 8 = 1 ∨ n % 8 = 7 := by
  have aux : ∀ n : ℕ, n ≠ 0 →
      (∀ p : ℕ, p.Prime → p ∣ n → p % 8 = 1 ∨ p % 8 = 7) →
      n % 8 = 1 ∨ n % 8 = 7 := by
    apply induction_on_primes
    · intro h
      exact (h rfl).elim
    · intro _ _
      norm_num
    · intro p a hp ih hpa hs
      have ha : a ≠ 0 := by
        intro h
        apply hpa
        simp [h]
      have hpm := hs p hp (dvd_mul_right p a)
      have ham := ih ha (fun q hq hqa => hs q hq (dvd_mul_of_dvd_right hqa p))
      rcases hpm with hpm | hpm <;> rcases ham with ham | ham <;>
        norm_num [Nat.mul_mod, hpm, ham]
  exact aux n hn hs

/-- A nonzero integer whose rational prime divisors are all congruent to
`1` or `7` modulo `8` is itself congruent to `1` or `7`, including either sign. -/
theorem int_mod_eight_of_prime_divisors (z : ℤ) (hz : z ≠ 0)
    (hs : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ z → p % 8 = 1 ∨ p % 8 = 7) :
    z % 8 = 1 ∨ z % 8 = 7 := by
  have habs : z.natAbs % 8 = 1 ∨ z.natAbs % 8 = 7 :=
    nat_mod_eight_of_prime_divisors z.natAbs
      (by simpa using hz)
      (fun p hp hpd => hs p hp (Int.natCast_dvd.mpr hpd))
  have hcast : (z.natAbs : ℤ) % 8 = 1 ∨ (z.natAbs : ℤ) % 8 = 7 := by
    exact_mod_cast habs
  rcases Int.natAbs_eq z with h | h
  · rw [h]
    exact hcast
  · rw [h]
    have hnd : ¬ (8 : ℤ) ∣ (z.natAbs : ℤ) := by
      intro hd
      have h0 := Int.emod_eq_zero_of_dvd hd
      omega
    rw [Int.neg_emod, if_neg hnd]
    rcases hcast with hc | hc <;> rw [hc] <;> norm_num

end FourCorner

#print axioms FourCorner.nat_mod_eight_of_prime_divisors
#print axioms FourCorner.int_mod_eight_of_prime_divisors
