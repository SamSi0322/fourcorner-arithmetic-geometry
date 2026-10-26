import HasseTangentScaling
namespace FourCorner.HassePoleParameters
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseInertPole HasseOddSymbol

/-- Exact factor of the original coefficient, using its actual conic. -/
def reducedCoefficient (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P) : ℚ :=
  (P.U+P.T+P.Z)*(D.w+2*P.U)+2*P.Z*(P.T+(p+1)*P.Z)

theorem secondCoefficient_factor (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P) :
    secondCoefficient p P D= -p^2*(p-1)*(p+1)*reducedCoefficient p P D := by
  dsimp [secondCoefficient,secondPolar,anchorU,anchorT,anchorZ,reducedCoefficient]
  linear_combination -2*p^2*(p+1)*P.equations.2.2

/-- At every pole, a and b have identical valuation. -/
theorem pole_a_valuation (Q : OddPrime) (p : ℚ) (hp : 1<p) (hv : padicValRat Q.val p<0) :
    (((p-1 : ℚ) : ℚ_[Q.val])).valuation=((p : ℚ_[Q.val])).valuation := by
  have hp0 : p ≠ 0 := by linarith
  have he := commonRoot_val_sub_of_ne (show (p : ℚ_[Q.val]) ≠ 0 by exact_mod_cast hp0)
    (one_ne_zero : (1 : ℚ_[Q.val]) ≠ 0)
    (by rw [Padic.valuation_ratCast,Padic.valuation_one]; omega)
  have heq : (p : ℚ_[Q.val])-1=((p-1 : ℚ) : ℚ_[Q.val]) := by simp
  rw [heq,Padic.valuation_one,min_eq_left (by rw [Padic.valuation_ratCast]; omega)] at he
  exact he

theorem pole_b_valuation (Q : OddPrime) (p : ℚ) (hp : 1<p) (hv : padicValRat Q.val p<0) :
    (((p+1 : ℚ) : ℚ_[Q.val])).valuation=((p : ℚ_[Q.val])).valuation := by
  have hp0 : p ≠ 0 := by linarith
  have he := commonRoot_val_add_of_ne (show (p : ℚ_[Q.val]) ≠ 0 by exact_mod_cast hp0)
    (one_ne_zero : (1 : ℚ_[Q.val]) ≠ 0)
    (by rw [Padic.valuation_ratCast,Padic.valuation_one]; omega)
  have heq : (p : ℚ_[Q.val])+1=((p+1 : ℚ) : ℚ_[Q.val]) := by simp
  rw [heq,Padic.valuation_one,min_eq_left (by rw [Padic.valuation_ratCast]; omega)] at he
  exact he

/-- This is a literal local square, not an assumed quaternion norm law. -/
theorem pole_b_div_a_square (Q : OddPrime) (p : ℚ) (hp : 1<p) (hv : padicValRat Q.val p<0) :
    IsSquare (((p+1)/(p-1) : ℚ) : ℚ_[Q.val]) := by
  have ha0 : p-1 ≠ 0 := by linarith
  have haq : (((p-1 : ℚ) : ℚ_[Q.val])) ≠ 0 := by exact_mod_cast ha0
  let y : ℚ_[Q.val] := ((p+1)/(p-1) : ℚ)
  have he : y-1=2/(((p-1 : ℚ) : ℚ_[Q.val])) := by
    dsimp [y]
    exact_mod_cast (show (p+1)/(p-1)-1=2/(p-1) from by field_simp; ring)
  have hne : y-1 ≠ 0 := by rw [he]; exact div_ne_zero (by norm_num) haq
  apply square_of_positive_perturbation Q 1 y one_ne_zero Padic.valuation_one IsSquare.one hne
  rw [he,commonRoot_val_div (by norm_num) haq,commonRoot_val_two Q.property.2,
    pole_a_valuation Q p hp hv,Padic.valuation_ratCast]
  omega

#print axioms secondCoefficient_factor
#print axioms pole_a_valuation
#print axioms pole_b_valuation
#print axioms pole_b_div_a_square
end FourCorner.HassePoleParameters
