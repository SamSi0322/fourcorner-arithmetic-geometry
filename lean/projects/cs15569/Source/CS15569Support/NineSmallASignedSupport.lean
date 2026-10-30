import FourCorner.CommonRootSupportDecomposition
import CS15569Support.NineCubicValuation

/-! Signed squarefree support for rational coordinates on integral cubics. -/
namespace FourCorner

/-- An integral target contains a squarefree natural precisely when it contains
all its prime factors. -/
theorem squarefree_nat_dvd_int_of_prime_support {n : ℕ} {b : ℤ}
    (hn : Squarefree n) (hb : b ≠ 0)
    (hs : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℤ) ∣ b) : (n : ℤ) ∣ b := by
  apply Int.natCast_dvd.mpr
  rw [← Nat.prod_primeFactors_of_squarefree hn]
  apply (Nat.prod_primeFactors_dvd_iff (Int.natAbs_ne_zero.mpr hb)).mpr
  intro p hp
  obtain ⟨hp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hp, Int.natCast_dvd.mp (hs p hp hpn),
    Int.natAbs_ne_zero.mpr hb⟩

/-- Signed squarefree normalization preserves every rational prime valuation,
including the prime two and primes in denominators. -/
theorem signed_squarefree_of_odd_valuation_support {b : ℤ} {x : ℚ}
    (hb : b ≠ 0) (hx : x ≠ 0)
    (hs : ∀ p : ℕ, p.Prime → Odd (padicValRat p x) → (p : ℤ) ∣ b) :
    ∃ d : ℤ, Squarefree d.natAbs ∧ d ∣ b ∧
      ∃ u : ℚ, 0 < u ∧ x = (d : ℚ) * u ^ 2 := by
  obtain ⟨n, hn, hns, u, hu, hxu⟩ :=
    positive_rat_squarefree_decomposition (abs_pos.mpr hx)
  have hdiv : (n : ℤ) ∣ b := by
    apply squarefree_nat_dvd_int_of_prime_support hns hb
    intro p hp hpn
    apply hs p hp
    rw [← padicValRat_abs_eq]
    exact squarefree_rat_mul_sq_prime_odd hns hp hpn hu.ne' hxu
  rcases le_total 0 x with hxpos | hxneg
  · refine ⟨n, by simpa using hns, hdiv, u, hu, ?_⟩
    simpa [abs_of_nonneg hxpos] using hxu
  · refine ⟨-(n : ℤ), by simpa using hns, neg_dvd.mpr hdiv, u, hu, ?_⟩
    rw [abs_of_nonpos hxneg] at hxu
    have heq := congrArg (fun z : ℚ => -z) hxu
    simpa using heq

/-- Every nonzero coordinate on an integral cubic has a signed squarefree
representative dividing the coefficient of its linear term. -/
theorem cubic_signed_squarefree_support {a b : ℤ} {x y : ℚ}
    (hb : b ≠ 0) (hx : x ≠ 0)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ d : ℤ, Squarefree d.natAbs ∧ d ∣ b ∧
      ∃ u : ℚ, 0 < u ∧ x = (d : ℚ) * u ^ 2 := by
  apply signed_squarefree_of_odd_valuation_support hb hx
  intro p hp hv
  exact cubic_odd_valuation_support hp hx hb h hv

/-- The only signed squarefree divisors of sixteen. -/
theorem signed_squarefree_divisor_sixteen {d : ℤ}
    (hs : Squarefree d.natAbs) (hd : d ∣ 16) :
    d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 := by
  have h16 : d.natAbs ∣ 2 ^ 4 := by
    have h := Int.natAbs_dvd_natAbs.mpr hd
    norm_num at h ⊢
    exact h
  have h2 : d.natAbs ∣ 2 := (hs.dvd_pow_iff_dvd (by decide : 4 ≠ 0)).mp h16
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ h2 with h1 | h2
  · rcases Int.natAbs_eq_iff.mp h1 with h | h <;> simp_all
  · rcases Int.natAbs_eq_iff.mp h2 with h | h <;> simp_all

/-- A squarefree divisor of forty-eight is supported at two and three. -/
theorem squarefree_divisor_fortyeight {n : ℕ}
    (hs : Squarefree n) (hd : n ∣ 48) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
  have hpow : n ∣ 6 ^ 4 := dvd_trans hd (by norm_num)
  have h6 : n ∣ 6 := (hs.dvd_pow_iff_dvd (by decide : 4 ≠ 0)).mp hpow
  have hm := Nat.mem_divisors.mpr ⟨h6, (by norm_num : 6 ≠ 0)⟩
  have he : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [he] at hm
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

/-- Positive abscissae admit positive squarefree representatives. -/
theorem cubic_positive_squarefree_support {a b : ℤ} {x y : ℚ}
    (hb : b ≠ 0) (hx : 0 < x)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ n : ℕ, Squarefree n ∧ n ∣ b.natAbs ∧
      ∃ u : ℚ, 0 < u ∧ x = (n : ℚ) * u ^ 2 := by
  obtain ⟨n, hn, hns, u, hu, hxu⟩ := positive_rat_squarefree_decomposition hx
  refine ⟨n, hns, ?_, u, hu, hxu⟩
  apply Int.natCast_dvd.mp
  apply squarefree_nat_dvd_int_of_prime_support hns hb
  intro p hp hpn
  exact cubic_odd_valuation_support hp hx.ne' hb h
    (squarefree_rat_mul_sq_prime_odd hns hp hpn hu.ne' hxu)

/-- The ordinary first slot of the cubic with roots zero, six and eight. -/
theorem smallA_first_slot {x y : ℚ} (hx : 0 < x)
    (h : y ^ 2 = x * (x - 6) * (x - 8)) :
    ∃ n : ℕ, (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6) ∧
      ∃ u : ℚ, 0 < u ∧ x = (n : ℚ) * u ^ 2 := by
  have hc : y ^ 2 = x ^ 3 + ((-14 : ℤ) : ℚ) * x ^ 2 + ((48 : ℤ) : ℚ) * x := by
    rw [h]; norm_num; ring
  obtain ⟨n, hn, hd, u, hu, heq⟩ := cubic_positive_squarefree_support (by norm_num) hx hc
  refine ⟨n, squarefree_divisor_fortyeight hn ?_, u, hu, heq⟩
  simpa using hd

/-- The ordinary third slot of the cubic with roots zero, six and eight,
with signs retained for points in the bounded real component. -/
theorem smallA_eight_slot {x y : ℚ} (hx : x - 8 ≠ 0)
    (h : y ^ 2 = x * (x - 6) * (x - 8)) :
    ∃ d : ℤ, (d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) ∧
      ∃ u : ℚ, 0 < u ∧ x - 8 = (d : ℚ) * u ^ 2 := by
  have hc : y ^ 2 = (x - 8) ^ 3 + ((10 : ℤ) : ℚ) * (x - 8) ^ 2 +
      ((16 : ℤ) : ℚ) * (x - 8) := by
    rw [h]; norm_num; ring
  obtain ⟨d, hd, hdiv, u, hu, heq⟩ := cubic_signed_squarefree_support (by norm_num) hx hc
  refine ⟨d, signed_squarefree_divisor_sixteen hd ?_, u, hu, heq⟩
  exact hdiv

end FourCorner
#print axioms FourCorner.signed_squarefree_of_odd_valuation_support

#print axioms FourCorner.cubic_signed_squarefree_support

#print axioms FourCorner.smallA_first_slot
#print axioms FourCorner.smallA_eight_slot
