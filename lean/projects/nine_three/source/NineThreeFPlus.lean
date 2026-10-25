import FourCorner.NineFlex
import SmallAComplete

/-! The F-plus branch of the uniform three-torsion exclusion. -/

namespace FourCorner.NineThree

/-- The signed flex quotient produces the literal rational point of the
auxiliary quartic used in the F-plus case. -/
theorem fplus_quartic_identity {t u k : ℚ} (hk : k ≠ 0)
    (hk1 : k ≠ 1) (hkm1 : k ≠ -1)
    (hT : t+1 = 2*u^2)
    (hratio : -t = (1+2*k)/((1-k)*(1+k)^3)) :
    (2*u*(1-k)*(1+k)^2/k)^2 = -2*k*(k+2)*(1-k^2) := by
  have hden : (1-k)*(1+k)^3 ≠ 0 := by
    apply mul_ne_zero
    · intro he; apply hk1; linarith
    · apply pow_ne_zero
      intro he; apply hkm1; linarith
  have hr := (eq_div_iff hden).mp hratio
  have hpoly : (2*u^2-1)*((1-k)*(1+k)^3)+(1+2*k)=0 := by
    linear_combination -hr - ((1-k)*(1+k)^3)*hT
  field_simp
  linear_combination (1-k^2)*hpoly

/-- For every real-chamber parameter the F-plus Weierstrass model is
elliptic, with its literal ordered roots. -/
theorem fplus_discriminant_ne_zero {t : ℚ} (ht : 1 < t) :
    (splitCurve (2*((t-1)*(t+1))) (-2*t*((t-1)*(t+1)))).Δ ≠ 0 := by
  apply (splitCurve_discriminant_ne_zero_iff _ _).mpr
  have hd : 0 < (t-1)*(t+1) := mul_pos (by linarith) (by linarith)
  have ha : 0 < 2*((t-1)*(t+1)) := by positivity
  have hb : -2*t*((t-1)*(t+1)) < 0 := by
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (by linarith)) hd
  exact ⟨ha.ne',hb.ne,ne_of_gt (lt_trans hb ha)⟩

/-- F-plus has no nonzero rational point annihilated by three in the actual
elliptic group whenever t+1 is twice a rational square. -/
theorem fplus_three_torsion_eq_zero {t u : ℚ} (ht : 1 < t)
    (hT : t+1=2*u^2)
    (P : (splitCurve (2*((t-1)*(t+1))) (-2*t*((t-1)*(t+1)))).toAffine.Point)
    (h3 : 3 • P=0) : P=0 := by
  by_contra hP
  obtain ⟨k,hk,hk1,hkm1,_,hkm2,hratio,r,hr,hA⟩ :=
    nine_flex (fplus_discriminant_ne_zero ht) P hP h3
  have hd : (t-1)*(t+1) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  have hquot : (-2*t*((t-1)*(t+1)))/(2*((t-1)*(t+1))) = -t := by
    apply (div_eq_iff (mul_ne_zero (by norm_num : (2:ℚ) ≠ 0) hd)).mpr
    ring
  rw [hquot] at hratio
  have hquartic := fplus_quartic_identity hk hk1 hkm1 hT hratio
  obtain ⟨_, hks⟩ := NineSmallA.complete_quartic_points hquartic
  rcases hks with hks|hks|hks|hks
  · exact hk hks
  · exact hkm2 hks
  · exact hk1 hks
  · exact hkm1 hks

/-- The same exclusion expressed through the actual additive order. -/
theorem fplus_addOrder_ne_three {t u : ℚ} (ht : 1 < t)
    (hT : t+1=2*u^2)
    (P : (splitCurve (2*((t-1)*(t+1))) (-2*t*((t-1)*(t+1)))).toAffine.Point) :
    addOrderOf P ≠ 3 := by
  intro h3
  have hkill : 3 • P=0 := by simpa only [h3] using addOrderOf_nsmul_eq_zero P
  have hP := fplus_three_torsion_eq_zero ht hT P hkill
  rw [hP] at h3
  norm_num at h3

end FourCorner.NineThree
#print axioms FourCorner.NineThree.fplus_quartic_identity
#print axioms FourCorner.NineThree.fplus_discriminant_ne_zero
#print axioms FourCorner.NineThree.fplus_three_torsion_eq_zero
#print axioms FourCorner.NineThree.fplus_addOrder_ne_three
