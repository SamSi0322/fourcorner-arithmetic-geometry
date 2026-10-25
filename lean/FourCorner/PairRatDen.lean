import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Exact reduced denominators and their prime valuations. -/

namespace FourCorner

/-- Reduction of an integer fraction cancels precisely the gcd of its
numerator and denominator. The formula permits either sign of `L`. -/
theorem rat_div_den_eq (A L : ℤ) (hL : L ≠ 0) :
    ((A : ℚ) / L).den = L.natAbs / Nat.gcd A.natAbs L.natAbs := by
  rw [← Rat.divInt_eq_div, Rat.den_divInt, if_neg hL]
  rw [Int.gcd_eq_natAbs_gcd_natAbs, Nat.gcd_comm]

/-- Positive-denominator form of the exact reduced-denominator formula. -/
theorem rat_div_den_eq_of_pos (A L : ℤ) (hL : 0 < L) :
    ((A : ℚ) / L).den = L.natAbs / Nat.gcd A.natAbs L.natAbs :=
  rat_div_den_eq A L (ne_of_gt hL)

/-- A prime's valuation of the gcd is the smaller of the two valuations. -/
theorem padicValNat_gcd_eq_min {p a b : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (Nat.gcd a b) = min (padicValNat p a) (padicValNat p b) := by
  simpa only [Nat.factorization_def _ hp, Finsupp.inf_apply] using
    congrArg (fun f : ℕ →₀ ℕ => f p) (Nat.factorization_gcd ha hb)

/-- Prime exponents in a reduced rational denominator are the truncated
difference between the original denominator and numerator exponents. -/
theorem padicValNat_rat_div_den_eq {p : ℕ} (hp : p.Prime)
    (A L : ℤ) (hA : A ≠ 0) (hL : L ≠ 0) :
    padicValNat p ((A : ℚ) / L).den =
      padicValNat p L.natAbs - padicValNat p A.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rat_div_den_eq A L hL,
    padicValNat.div_of_dvd (Nat.gcd_dvd_right A.natAbs L.natAbs),
    padicValNat_gcd_eq_min hp (Int.natAbs_ne_zero.mpr hA) (Int.natAbs_ne_zero.mpr hL)]
  omega

end FourCorner

#print axioms FourCorner.rat_div_den_eq
#print axioms FourCorner.padicValNat_gcd_eq_min
#print axioms FourCorner.padicValNat_rat_div_den_eq
