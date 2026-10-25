import FourCorner.PairRatDen
import Mathlib.Tactic.Ring

namespace FourCorner

/-- Divisibility increases the finite prime valuation when the larger integer
is nonzero. -/
theorem padicValNat_natAbs_le_of_dvd {p : ℕ} (hp : p.Prime)
    {a b : ℤ} (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a.natAbs ≤ padicValNat p b.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  apply (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hb)).mp
  exact pow_padicValNat_dvd.trans (Int.natAbs_dvd_natAbs.mpr h)

/-- Two odd integers have even sum and difference, but exactly one of their
sum and difference is divisible by four. In valuation form, the minimum is one. -/
theorem odd_pair_min_two_valuation {a b : ℤ} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hs : a + b ≠ 0) (hd : a - b ≠ 0) :
    min (padicValNat 2 (a + b).natAbs) (padicValNat 2 (a - b).natAbs) = 1 := by
  have hs2 : (2 : ℤ) ∣ a + b := by omega
  have hd2 : (2 : ℤ) ∣ a - b := by omega
  have hs1 : 1 ≤ padicValNat 2 (a + b).natAbs :=
    one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hs)
      (by simpa using (Int.natAbs_dvd_natAbs.mpr hs2))
  have hd1 : 1 ≤ padicValNat 2 (a - b).natAbs :=
    one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hd)
      (by simpa using (Int.natAbs_dvd_natAbs.mpr hd2))
  have hn : ¬(2 ≤ padicValNat 2 (a + b).natAbs ∧
      2 ≤ padicValNat 2 (a - b).natAbs) := by
    rintro ⟨hs4, hd4⟩
    have hs4' : (4 : ℤ) ∣ a + b := by
      have h := (padicValNat_dvd_iff_le (p := 2) (Int.natAbs_ne_zero.mpr hs)).mpr hs4
      exact Int.natAbs_dvd_natAbs.mp (by simpa using h)
    have hd4' : (4 : ℤ) ∣ a - b := by
      have h := (padicValNat_dvd_iff_le (p := 2) (Int.natAbs_ne_zero.mpr hd)).mpr hd4
      exact Int.natAbs_dvd_natAbs.mp (by simpa using h)
    omega
  omega

/-- The exact dyadic contribution from the sum and difference of two odd
integers. The double-denominator divisibility forces one reduced denominator
to be odd and the other to contain precisely one fewer factor of two than `L`. -/
theorem odd_pair_den_two_valuation {a b L : ℤ}
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hL : 0 < L)
    (h8 : (8 : ℤ) ∣ L) (hdiv : 2 * L ∣ a ^ 2 - b ^ 2)
    (hne : a ≠ b) (hs : a + b ≠ 0) :
    padicValNat 2 (((a + b : ℤ) : ℚ) / L).den +
        padicValNat 2 (((a - b : ℤ) : ℚ) / L).den =
      padicValNat 2 L.natAbs - 1 ∧
    min (padicValNat 2 (((a + b : ℤ) : ℚ) / L).den)
      (padicValNat 2 (((a - b : ℤ) : ℚ) / L).den) = 0 := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hL0 := ne_of_gt hL
  have he : 3 ≤ padicValNat 2 L.natAbs := by
    apply (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hL0)).mp
    simpa using (Int.natAbs_dvd_natAbs.mpr h8)
  have hmin := odd_pair_min_two_valuation ha hb hs hd
  have hprod : 2 * L ∣ (a + b) * (a - b) := by
    convert hdiv using 1; ring
  have hval := padicValNat_natAbs_le_of_dvd Nat.prime_two
    (mul_ne_zero hs hd) hprod
  simp only [Int.natAbs_mul] at hval
  rw [padicValNat.mul (by decide) (Int.natAbs_ne_zero.mpr hL0),
    padicValNat.mul (Int.natAbs_ne_zero.mpr hs) (Int.natAbs_ne_zero.mpr hd)] at hval
  norm_num at hval
  rw [padicValNat_rat_div_den_eq Nat.prime_two _ _ hs hL0,
    padicValNat_rat_div_den_eq Nat.prime_two _ _ hd hL0]
  omega

end FourCorner

#print axioms FourCorner.odd_pair_min_two_valuation
#print axioms FourCorner.odd_pair_den_two_valuation
