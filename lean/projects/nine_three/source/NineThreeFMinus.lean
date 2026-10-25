import FourCorner.NineFlex
import FourCorner.RatIntegralAux
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace FourCorner.NineThree

private theorem int_square_not_two_mod_four (z:ℤ) : z^2%4≠2 := by
  simpa [pow_two] using Int.sq_ne_two_mod_four z

private theorem first_conic_even {u v w:ℤ} (h:w^2=2*u*(u+2*v)) : u%2=0 := by
  have hs := int_square_not_two_mod_four w
  rw [h] at hs
  have hu0 := Int.emod_nonneg u (by norm_num : (4:ℤ)≠0)
  have hu4 := Int.emod_lt_of_pos u (by norm_num : (0:ℤ)<4)
  have hv0 := Int.emod_nonneg v (by norm_num : (4:ℤ)≠0)
  have hv4 := Int.emod_lt_of_pos v (by norm_num : (0:ℤ)<4)
  interval_cases hu:u%4 <;> interval_cases hv:v%4 <;>
    norm_num [Int.mul_emod,Int.add_emod,hu,hv] at hs <;> omega

/-- Two simultaneous rational-square conditions forced by F-minus would
contradict the exact dyadic residue of their second numerator. -/
theorem fminus_parameter_impossible (k w z:ℚ)
    (hw:w^2=2*k*(k+2))
    (hz:z^2*((1-k)*(1+k)^3)=2+4*k-2*k^3-k^4) : False := by
  let u : ℤ := k.num
  let v : ℤ := k.den
  have hv : (0:ℤ)<v := by dsimp [v]; exact_mod_cast k.den_pos
  have hvq : (v:ℚ)≠0 := by exact_mod_cast ne_of_gt hv
  have hk : k=(u:ℚ)/(v:ℚ) := by
    dsimp [u,v]
    simpa using (Rat.num_div_den k).symm
  rw [hk] at hw hz
  field_simp at hw hz
  have hwi : (w*(v:ℚ))^2=((2*u*(u+2*v):ℤ):ℚ) := by
    push_cast
    linear_combination hw
  obtain ⟨W,hW⟩ := exists_int_of_sq_eq_int hwi
  have hWint : W^2=2*u*(u+2*v) := by
    have hh:=hwi
    rw [hW] at hh
    exact_mod_cast hh
  have hue := first_conic_even hWint
  have hvo : v%2=1 := by
    have hcop : Nat.Coprime u.natAbs v.natAbs := by simpa [u,v] using k.reduced
    have hu2 : 2∣u.natAbs := Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero hue)
    by_contra hn
    have hv2 : 2∣v.natAbs := Int.natCast_dvd.mp (show (2:ℤ)∣v by omega)
    have hg := Nat.dvd_gcd hu2 hv2
    rw [hcop] at hg
    norm_num at hg
  let D : ℤ := (v-u)*(v+u)^3
  let N : ℤ := 2*v^4+4*u*v^3-2*u^3*v-u^4
  have hzi : (z*(D:ℚ))^2=((N*D:ℤ):ℚ) := by
    dsimp [D,N]
    push_cast
    linear_combination (((v:ℚ)-(u:ℚ))*((v:ℚ)+(u:ℚ))^3)*hz
  obtain ⟨Z,hZ⟩ := exists_int_of_sq_eq_int hzi
  have hZint : Z^2=N*D := by
    have hh:=hzi
    rw [hZ] at hh
    exact_mod_cast hh
  have hs := int_square_not_two_mod_four Z
  rw [hZint] at hs
  dsimp [N,D] at hs
  have hu0 := Int.emod_nonneg u (by norm_num : (4:ℤ)≠0)
  have hu4 := Int.emod_lt_of_pos u (by norm_num : (0:ℤ)<4)
  have hv0 := Int.emod_nonneg v (by norm_num : (4:ℤ)≠0)
  have hv4 := Int.emod_lt_of_pos v (by norm_num : (0:ℤ)<4)
  interval_cases hu:u%4 <;> interval_cases hv:v%4 <;>
    norm_num [Int.mul_emod,Int.add_emod,Int.sub_emod,pow_succ,Int.mul_emod,Int.add_emod,Int.sub_emod,hu,hv] at hs <;> omega

end FourCorner.NineThree
#print axioms FourCorner.NineThree.fminus_parameter_impossible

namespace FourCorner.NineThree

/-- The literal F-minus cubic is nonsingular throughout t>1. -/
theorem fminus_discriminant_ne_zero {t:ℚ} (ht:1<t) :
    (splitCurve (2*((t-1)*(t+1))) (2*t*((t-1)*(t+1)))).Δ≠0 := by
  have hd : 0<(t-1)*(t+1) := mul_pos (by linarith) (by linarith)
  apply (splitCurve_discriminant_ne_zero_iff _ _).mpr
  refine ⟨by positivity,by positivity,?_⟩
  have hprod := mul_pos (show 0<t-1 by linarith) hd
  intro he
  nlinarith

/-- Every actual rational F-minus point annihilated by three is infinity,
when t>1 and t+1 is a rational square. -/
theorem fminus_three_torsion_eq_zero {t z:ℚ} (ht:1<t) (hT:t+1=z^2)
    (P:(splitCurve (2*((t-1)*(t+1))) (2*t*((t-1)*(t+1)))).toAffine.Point)
    (h3:3 • P=0) : P=0 := by
  by_contra hP
  have hd : 0<(t-1)*(t+1) := mul_pos (by linarith) (by linarith)
  have hdz : (t-1)*(t+1)≠0 := ne_of_gt hd
  have hz : z≠0 := by intro hz; rw [hz] at hT; nlinarith
  obtain ⟨k,hk,hk1,hkm1,hkmhalf,hkm2,hR,r,hr,hrA⟩ :=
    nine_flex (fminus_discriminant_ne_zero ht) P hP h3
  have hratio : (2*t*((t-1)*(t+1)))/(2*((t-1)*(t+1)))=t := by
    apply (div_eq_iff (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hdz)).mpr
    ring
  rw [hratio] at hR
  have hkplus : 1+k≠0 := by intro h; apply hkm1; linarith
  have hkminus : 1-k≠0 := by intro h; apply hk1; linarith
  have hD : (1-k)*(1+k)^3≠0 := mul_ne_zero hkminus (pow_ne_zero _ hkplus)
  have hRD : t*((1-k)*(1+k)^3)=1+2*k := (eq_div_iff hD).mp hR
  have hshift : (t-1)*((1-k)*(1+k)^3)=k^3*(k+2) := by
    linear_combination hRD
  have hnum : r^2*((1-k)*(1+k)^2)^2=2*k^3*(k+2)*z^2 := by
    linear_combination -((1-k)*(1+k)^3)*hrA+
      2*(t+1)*hshift+2*k^3*(k+2)*hT
  have hw : (r*((1-k)*(1+k)^2)/(z*k))^2=2*k*(k+2) := by
    field_simp
    linear_combination hnum
  have hzD : z^2*((1-k)*(1+k)^3)=2+4*k-2*k^3-k^4 := by
    linear_combination hRD-((1-k)*(1+k)^3)*hT
  exact fminus_parameter_impossible k (r*((1-k)*(1+k)^2)/(z*k)) z hw hzD

/-- The preceding theorem with literal additive order. -/
theorem fminus_addOrder_ne_three {t z:ℚ} (ht:1<t) (hT:t+1=z^2)
    (P:(splitCurve (2*((t-1)*(t+1))) (2*t*((t-1)*(t+1)))).toAffine.Point) :
    addOrderOf P≠3 := by
  intro h
  have h3 : 3 • P=0 := by simpa only [h] using addOrderOf_nsmul_eq_zero P
  have hP := fminus_three_torsion_eq_zero ht hT P h3
  rw [hP] at h
  simpa using h

end FourCorner.NineThree
#print axioms FourCorner.NineThree.fminus_three_torsion_eq_zero
#print axioms FourCorner.NineThree.fminus_addOrder_ne_three
