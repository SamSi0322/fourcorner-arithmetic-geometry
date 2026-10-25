import FourCorner.ReciprocityOddPart
import FourCorner.SupportProductEight
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

namespace FourCorner

/-- The number of distinct prime divisors congruent to seven modulo eight. -/
def sevenPrimeCount (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p => p % 8 = 7)).card

@[simp] theorem sevenPrimeCount_one : sevenPrimeCount 1 = 0 := by
  simp [sevenPrimeCount]

private lemma chi4_product_seven_card (S : Finset ℕ)
    (hS : ∀ p ∈ S, p % 8 = 1 ∨ p % 8 = 7) :
    ZMod.χ₄ ((∏ p ∈ S, p : ℕ) : ZMod 4) =
      (-1 : ℤ) ^ (S.filter (fun p => p % 8 = 7)).card := by
  calc
    ZMod.χ₄ ((∏ p ∈ S, p : ℕ) : ZMod 4) = ∏ p ∈ S, ZMod.χ₄ p := by
      simp only [Nat.cast_prod, map_prod]
    _ = ∏ p ∈ S, (if p % 8 = 7 then (-1 : ℤ) else 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      rcases hS p hp with h | h
      · rw [ZMod.χ₄_nat_one_mod_four (by omega), if_neg (by omega)]
      · rw [ZMod.χ₄_nat_three_mod_four (by omega), if_pos h]
    _ = _ := by rw [Finset.prod_ite]; simp

private lemma sign_parity_eq {a b : ℕ} (hb : b ≤ 1)
    (h : (-1 : ℤ) ^ a = (-1) ^ b) : a % 2 = b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · apply Nat.even_iff.mp
    apply (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num)).mp
    simpa using h
  · apply Nat.odd_iff.mp
    apply (neg_one_pow_eq_neg_one_iff_odd (R := ℤ) (by norm_num)).mp
    simpa using h

/-- On positive squarefree integers supported on primes one or seven modulo
eight, the residue parity `e4` is literally the parity of the number of
seven-modulo-eight prime factors. This includes the empty factorization of one. -/
theorem sevenPrimeCount_parity {n : ℕ} (hnpos : 0 < n) (hn : Squarefree n)
    (hs : ∀ p : ℕ, p.Prime → p ∣ n → p % 8 = 1 ∨ p % 8 = 7) :
    sevenPrimeCount n % 2 = e4 n := by
  have hn8 := nat_mod_eight_of_prime_divisors n hnpos.ne' hs
  have hodd : Odd n := Nat.odd_iff.mpr (by rcases hn8 with h | h <;> omega)
  have hc := chi4_product_seven_card n.primeFactors (fun p hp =>
    hs p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1)
  rw [Nat.prod_primeFactors_of_squarefree hn, chi4_eq_neg_one_pow_e4 hodd] at hc
  apply sign_parity_eq (b := e4 n)
  · unfold e4
    split_ifs <;> omega
  · exact hc.symm

end FourCorner

#print axioms FourCorner.sevenPrimeCount_parity
