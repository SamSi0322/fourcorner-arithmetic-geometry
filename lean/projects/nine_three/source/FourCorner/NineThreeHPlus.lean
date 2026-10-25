import FourCorner.NineFlex
import FourCorner.NineThreeHPlusArithmetic

namespace FourCorner

/-- The nonsingularity of the actual H-plus curve follows from t > 1. -/
theorem nine_hplus_discriminant_ne_zero {t : ℚ} (ht : 1 < t) :
    (splitCurve (2 * (t + 1)) ((t + 1)^2)).Δ ≠ 0 := by
  apply (splitCurve_discriminant_ne_zero_iff _ _).2
  have hT : 2 < t + 1 := by linarith
  refine ⟨by positivity, by positivity, ?_⟩
  intro he
  nlinarith

/-- On H-plus, the full flex data and a rational square T produce the
rational quartic which supplies the two-adic contradiction. -/
theorem nine_hplus_flex_quartic {T k r : ℚ}
    (hT : IsSquare T) (hTn : T ≠ 0)
    (hk1 : k ≠ 1) (hkm1 : k ≠ -1) (hr : r ≠ 0)
    (hratio : T^2 / (2*T) = (1+2*k)/((1-k)*(1+k)^3))
    (hAr : 2*T = r^2*(1-k^2)) :
    ∃ a b : ℚ, 8*b^2 = 3 + 2*a^2 - a^4 := by
  obtain ⟨s, hs⟩ := hT
  have hminus : 1-k ≠ 0 := by intro he; apply hk1; linarith
  have hplus : 1+k ≠ 0 := by intro he; apply hkm1; linarith
  have hD : (1-k)*(1+k)^3 ≠ 0 := mul_ne_zero hminus (pow_ne_zero _ hplus)
  have hcancel : T^2 / (2*T) = T/2 := by
    apply (div_eq_div_iff (mul_ne_zero (by norm_num) hTn) (by norm_num)).2
    ring
  have hR : T/2 = (1+2*k)/((1-k)*(1+k)^3) := by
    rwa [hcancel] at hratio
  have hTD : T*((1-k)*(1+k)^3) = 2*(1+2*k) := by
    have he := (eq_div_iff hD).1 hR
    linarith
  let a : ℚ := r*(1-k)*(1+k)^2/2
  let b : ℚ := s/r
  have ha : a^2 = 1+2*k := by
    dsimp [a]
    linear_combination (-((1-k)*(1+k)^3)/4)*hAr + (1/2)*hTD
  have hb : 1-k^2 = 2*b^2 := by
    dsimp [b]
    field_simp
    nlinarith [hs, hAr]
  refine ⟨a, b, ?_⟩
  have ha2 := congrArg (fun z : ℚ => z^2) ha
  nlinarith

/-- H-plus has no nonzero point killed by three whenever T = t+1 is square.
The point is in Mathlib's actual affine group, and t > 1 supplies the
nonsingular discriminant without an additional assumption. -/
theorem nine_hplus_no_nonzero_three_torsion {t : ℚ} (ht : 1 < t)
    (hT : IsSquare (t+1))
    (P : (splitCurve (2*(t+1)) ((t+1)^2)).toAffine.Point)
    (hP : P ≠ 0) : 3 • P ≠ 0 := by
  intro h3
  obtain ⟨k, hk0, hk1, hkm1, hkmhalf, hkm2, hratio, r, hr, hAr⟩ :=
    nine_flex (nine_hplus_discriminant_ne_zero ht) P hP h3
  obtain ⟨a, b, hab⟩ := nine_hplus_flex_quartic hT (by linarith) hk1 hkm1 hr
    hratio hAr
  exact NineThreeHPlus.hplus_quartic_no_rational_point a b hab

/-- The rational three-torsion subgroup of H-plus is trivial. -/
theorem nine_hplus_three_torsion_eq_zero {t : ℚ} (ht : 1 < t)
    (hT : IsSquare (t+1))
    (P : (splitCurve (2*(t+1)) ((t+1)^2)).toAffine.Point)
    (h3 : 3 • P = 0) : P = 0 := by
  by_contra hP
  exact nine_hplus_no_nonzero_three_torsion ht hT P hP h3

/-- Equivalent exact-order formulation for the actual affine group. -/
theorem nine_hplus_no_addOrder_three {t : ℚ} (ht : 1 < t)
    (hT : IsSquare (t+1))
    (P : (splitCurve (2*(t+1)) ((t+1)^2)).toAffine.Point) :
    addOrderOf P ≠ 3 := by
  intro ho
  have hP : P ≠ 0 := by
    intro he
    rw [he] at ho
    simp at ho
  apply nine_hplus_no_nonzero_three_torsion ht hT P hP
  simpa only [ho] using addOrderOf_nsmul_eq_zero P

#print axioms nine_hplus_discriminant_ne_zero
#print axioms nine_hplus_flex_quartic
#print axioms nine_hplus_no_nonzero_three_torsion
#print axioms nine_hplus_three_torsion_eq_zero
#print axioms nine_hplus_no_addOrder_three
end FourCorner
