import EllipticCurves.Mathlib.Basic

namespace Units.modPow

variable {K : Type*} [Field K]

/-- Equality of signed square classes is tested by the literal scalar ratio. -/
theorem signedUnits_mk0_eq_iff (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (QuotientGroup.mk (Units.mk0 a ha) : Units.modPow K 2) =
      QuotientGroup.mk (Units.mk0 b hb) ↔ IsSquare (a / b) := by
  rw [← div_eq_one, ← QuotientGroup.mk_div, mk_eq_one_iff_isSquare]
  simp only [Units.val_div_eq_div_val, Units.val_mk0]

/-- Equivalent witness form, with no loss of signs. -/
theorem signedUnits_mk0_eq_iff_exists (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (QuotientGroup.mk (Units.mk0 a ha) : Units.modPow K 2) =
      QuotientGroup.mk (Units.mk0 b hb) ↔ ∃ q : K, a = b * q ^ 2 := by
  rw [signedUnits_mk0_eq_iff, isSquare_iff_exists_sq]
  exact exists_congr fun q ↦ by rw [div_eq_iff hb, mul_comm (q ^ 2) b]

#print axioms signedUnits_mk0_eq_iff
#print axioms signedUnits_mk0_eq_iff_exists

end Units.modPow
