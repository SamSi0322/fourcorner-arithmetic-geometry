import HassePositiveAEven
import HasseInertSupport

namespace FourCorner.HasseInertPole
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseOddSymbol HasseInertSupport

/-- Square lifting at any valuation, including poles and arbitrary negative
depth. This is derived directly from the proved odd-prime Hensel criterion. -/
theorem square_of_higher_valuation_perturbation (Q : OddPrime) (x y : ℚ_[Q.val])
    (hx : x ≠ 0) (hsq : IsSquare x) (hne : y-x ≠ 0)
    (hv : x.valuation<(y-x).valuation) : IsSquare y := by
  apply padic_odd_isSquare_of_norm_sub_lt Q.property.2 hx hsq
  have hdiv : (y-x)/x ≠ 0 := div_ne_zero hne hx
  have hval : 0<((y-x)/x).valuation := by
    rw [commonRoot_val_div hne hx]
    omega
  have hn := (commonRoot_norm_lt_one_iff hdiv).mpr hval
  rw [norm_div] at hn
  exact (div_lt_one (norm_pos_iff.mpr hx)).mp hn

/-- An inert pole forces the actual first coefficient to be a local square,
using the original source V equation and the derived t/z-integrality. -/
theorem firstCoefficient_square_at_inert_pole (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h2 : ¬ IsSquare (2 : ℚ_[Q.val])) (hv : padicValRat Q.val p<0) :
    IsSquare (firstCoefficient p : ℚ_[Q.val]) := by
  have hp0 : p ≠ 0 := by linarith
  obtain ⟨hZ,hU,hV,hW,hT⟩ := coordinates_ne_zero p hp P
  let pp : ℚ_[Q.val] := p
  let t : ℚ_[Q.val] := (P.T/P.Z : ℚ)
  let v : ℚ_[Q.val] := (P.V/P.Z : ℚ)
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
  have ht : t ≠ 0 := by dsimp [t]; exact_mod_cast div_ne_zero hT hZ
  have hv0 : v ≠ 0 := by dsimp [v]; exact_mod_cast div_ne_zero hV hZ
  have htv : 0≤t.valuation := by
    have he := (source_support Q p hp P D h2).1
    dsimp [t]
    rwa [Padic.valuation_ratCast]
  have hpv : pp.valuation<0 := by dsimp [pp]; rwa [Padic.valuation_ratCast]
  have he : v^2=2*t^2-4*pp := by
    have hr : (P.V/P.Z)^2=2*(P.T/P.Z)^2-4*p := by
      field_simp
      linear_combination D.omission.1
    dsimp [v,t,pp]
    exact_mod_cast hr
  have htwo : (2 : ℚ_[Q.val]) ≠ 0 := by norm_num
  have hfour : (4 : ℚ_[Q.val]) ≠ 0 := by norm_num
  have hfourval : (4 : ℚ_[Q.val]).valuation=0 := by
    have heq : (4 : ℚ_[Q.val])=2^2 := by norm_num
    rw [heq,Padic.valuation_pow,commonRoot_val_two Q.property.2]
    simp
  have htwo_t : (2*t^2).valuation≥0 := by
    rw [Padic.valuation_mul htwo (pow_ne_zero _ ht),commonRoot_val_two Q.property.2,Padic.valuation_pow]
    omega
  have hfour_p : (4*pp).valuation=pp.valuation := by
    rw [Padic.valuation_mul hfour hpq,hfourval,zero_add]
  have hvval : (v^2/4).valuation=pp.valuation := by
    rw [commonRoot_val_div (pow_ne_zero _ hv0) hfour,he,
      commonRoot_val_sub_of_ne (mul_ne_zero htwo (pow_ne_zero _ ht)) (mul_ne_zero hfour hpq)
        (by omega : (2*t^2).valuation ≠ (4*pp).valuation),
      hfourval,hfour_p,sub_zero]
    exact min_eq_right (by omega)
  let x : ℚ_[Q.val] := v^2/4
  let y : ℚ_[Q.val] := firstCoefficient p
  have hx : x ≠ 0 := div_ne_zero (pow_ne_zero _ hv0) hfour
  have hxsq : IsSquare x := by
    have heq : x=(v/2)^2 := by dsimp [x]; ring
    rw [heq]
    exact IsSquare.sq _
  have hdiff : y-x=1-t^2/2 := by
    dsimp [y,x,firstCoefficient]
    push_cast
    rw [he]
    dsimp [pp]
    ring
  by_cases hd : y-x=0
  · have heq : y=x := sub_eq_zero.mp hd
    change IsSquare y
    rwa [heq]
  have hdiffv : 0≤(y-x).valuation := by
    rw [hdiff]
    have hne : (1 : ℚ_[Q.val])+ -(t^2/2) ≠ 0 := by simpa only [← sub_eq_add_neg,← hdiff] using hd
    have hh := Padic.le_valuation_add (x:=(1 : ℚ_[Q.val])) (y:=-(t^2/2)) hne
    rw [← sub_eq_add_neg,Padic.valuation_one,commonRoot_val_neg,
      commonRoot_val_div (pow_ne_zero _ ht) htwo,Padic.valuation_pow,
      commonRoot_val_two Q.property.2] at hh
    omega
  exact square_of_higher_valuation_perturbation Q x y hx hxsq hd (by change (v^2/4).valuation<(y-x).valuation; omega)

theorem tangentSign_inert_pole (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h2 : ¬ IsSquare (2 : ℚ_[Q.val])) (hv : padicValRat Q.val p<0) :
    tangentSign p hp P D Q.val=1 := by
  rw [tangentSign,rationalSign_eq_oddSign]
  exact oddSign_one_of_left_square Q _ _ _ _
    (firstCoefficient_square_at_inert_pole Q p hp P D h2 hv)

#print axioms square_of_higher_valuation_perturbation
#print axioms firstCoefficient_square_at_inert_pole
#print axioms tangentSign_inert_pole
end FourCorner.HasseInertPole
