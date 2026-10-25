import FourCorner.NineFlex
import E0Complete

namespace FourCorner

/-- The literal elliptic factor `G_t` in the nine-factor decomposition. -/
def nineGCurve (t : ℚ) : WeierstrassCurve ℚ :=
  splitCurve (((t-1)*(t+1))^2) (-((t-1)*(t+1)))

theorem nineGCurve_discriminant_ne_zero {t : ℚ}
    (ht : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    (nineGCurve t).Δ ≠ 0 := by
  have hm : t-1 ≠ 0 := sub_ne_zero.mpr ht1
  have hp : t+1 ≠ 0 := by intro hz; apply htm1; linarith
  have hd : (t-1)*(t+1) ≠ 0 := mul_ne_zero hm hp
  apply (splitCurve_discriminant_ne_zero_iff _ _).mpr
  refine ⟨pow_ne_zero 2 hd, neg_ne_zero.mpr hd, ?_⟩
  intro h
  have hz : ((t-1)*(t+1)) * t^2 = 0 := by nlinarith [h]
  exact (mul_ne_zero hd (pow_ne_zero 2 ht)) hz

theorem nineGCurve_isElliptic {t : ℚ}
    (ht : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    (nineGCurve t).IsElliptic :=
  ⟨(nineGCurve_discriminant_ne_zero ht ht1 htm1).isUnit⟩

/-- Clearing the flex ratio yields the exact equation that returns to E0. -/
lemma nineG_flex_relation {t k : ℚ} (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (hk1 : k ≠ 1) (hkm1 : k ≠ -1)
    (hR : (-((t-1)*(t+1))) / (((t-1)*(t+1))^2) =
      (1+2*k)/((1-k)*(1+k)^3)) :
    t^2*(1+2*k) = k^3*(k+2) := by
  have hp : t+1 ≠ 0 := by intro hz; apply htm1; linarith
  have hd : (t-1)*(t+1) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr ht1) hp
  have hkplus : 1+k ≠ 0 := by intro hz; apply hkm1; linarith
  have hkminus : 1-k ≠ 0 := by intro hz; apply hk1; linarith
  have hD : (1-k)*(1+k)^3 ≠ 0 := mul_ne_zero hkminus (pow_ne_zero 3 hkplus)
  have hc := (div_eq_div_iff (pow_ne_zero 2 hd) hD).mp hR
  have hf : ((t-1)*(t+1)) *
      ((1-k)*(1+k)^3 + ((t-1)*(t+1))*(1+2*k)) = 0 := by
    nlinarith [hc]
  have hg := (mul_eq_zero.mp hf).resolve_left hd
  nlinarith [hg]

/-- The point on E0 is constructed from the same flex parameter and t. -/
lemma nineG_flex_to_E0 {t k : ℚ} (hk : k ≠ 0)
    (h : t^2*(1+2*k) = k^3*(k+2)) :
    (2*t*(1+2*k)/k)^2 = (2*k)*(2*k+1)*(2*k+4) := by
  field_simp
  linear_combination 2*(1+2*k)*h

/-- The actual rational point group of G_t has trivial three-torsion. -/
theorem nineG_no_nonzero_three_torsion {t : ℚ}
    (ht : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (P : (nineGCurve t).toAffine.Point) (h3 : 3 • P = 0) : P = 0 := by
  by_contra hP
  obtain ⟨k,hk,hk1,hkm1,hkmhalf,hkm2,hR,_⟩ :=
    nine_flex (nineGCurve_discriminant_ne_zero ht ht1 htm1) P hP h3
  have hrel := nineG_flex_relation ht1 htm1 hk1 hkm1 hR
  have he0 := nineG_flex_to_E0 hk hrel
  rcases NineSmallE0.complete_rational_points he0 with
    ⟨hx,_⟩ | ⟨hx,_⟩ | ⟨hx,_⟩ | ⟨hx,_⟩ | ⟨hx,_⟩
  · exact hk (by linarith)
  · exact hkmhalf (by linarith)
  · exact hkm2 (by linarith)
  · exact hk1 (by linarith)
  · exact hkm1 (by linarith)

theorem nineG_no_order_three {t : ℚ}
    (ht : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (P : (nineGCurve t).toAffine.Point) : addOrderOf P ≠ 3 := by
  intro h
  have h3 : 3 • P = 0 := by simpa only [h] using addOrderOf_nsmul_eq_zero P
  have hz := nineG_no_nonzero_three_torsion ht ht1 htm1 P h3
  rw [hz] at h
  simp at h

end FourCorner

#print axioms FourCorner.nineGCurve_discriminant_ne_zero
#print axioms FourCorner.nineGCurve_isElliptic
#print axioms FourCorner.nineG_flex_relation
#print axioms FourCorner.nineG_flex_to_E0
#print axioms FourCorner.nineG_no_nonzero_three_torsion
#print axioms FourCorner.nineG_no_order_three
