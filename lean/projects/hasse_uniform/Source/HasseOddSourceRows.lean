import HasseOddSymbol
import HasseTangentGlobal

/-! Genuine completed-field evaluations of the constructed rational tangent
symbol. These rows use all source parameters and arbitrary valuation depth. -/
namespace FourCorner.HasseOddSourceRows

open HilbertArithmeticHigh11 HasseOddSymbol HasseTangentGlobal
open HasseRationalSource HasseAnchorChoice

/-- The full positive-p row of the odd-prime table, at every depth. -/
theorem tangentSign_positive_p (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hv : 0<padicValRat q.val p) :
    tangentSign p hp P D q.val=1 := by
  have hp0 : p ≠ 0 := by linarith
  have hpq : (p : ℚ_[q.val]) ≠ 0 := by exact_mod_cast hp0
  have hc : IsSquare (firstCoefficient p : ℚ_[q.val]) := by
    apply square_of_positive_perturbation q 1 (firstCoefficient p : ℚ_[q.val])
      one_ne_zero Padic.valuation_one IsSquare.one
    · have he : (firstCoefficient p : ℚ_[q.val])-1= -(p : ℚ_[q.val]) := by
        simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one]
        ring
      rw [he]
      exact neg_ne_zero.mpr hpq
    · have he : (firstCoefficient p : ℚ_[q.val])-1= -(p : ℚ_[q.val]) := by
        simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one]
        ring
      rw [he,commonRoot_val_neg,Padic.valuation_ratCast]
      exact hv
  rw [tangentSign,rationalSign_eq_oddSign]
  exact oddSign_one_of_left_square q _ _ _ _ hc

/-- The split positive-b row of the table, again at every positive depth. -/
theorem tangentSign_positive_b_split (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : 0<padicValRat q.val (p+1)) (h2 : IsSquare (2 : ℚ_[q.val])) :
    tangentSign p hp P D q.val=1 := by
  have hb0 : p+1 ≠ 0 := by linarith
  have hbq : (p : ℚ_[q.val])+1 ≠ 0 := by exact_mod_cast hb0
  have hc : IsSquare (firstCoefficient p : ℚ_[q.val]) := by
    apply square_of_positive_perturbation q 2 (firstCoefficient p : ℚ_[q.val])
      (by norm_num) (commonRoot_val_two q.property.2) h2
    · have he : (firstCoefficient p : ℚ_[q.val])-2= -((p : ℚ_[q.val])+1) := by
        simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one]
        ring
      rw [he]
      exact neg_ne_zero.mpr hbq
    · have he : (firstCoefficient p : ℚ_[q.val])-2= -((p : ℚ_[q.val])+1) := by
        simp only [firstCoefficient,Rat.cast_neg,Rat.cast_sub,Rat.cast_one]
        ring
      rw [he,commonRoot_val_neg]
      have heq : (p : ℚ_[q.val])+1=((p+1 : ℚ) : ℚ_[q.val]) := by simp
      rw [heq,Padic.valuation_ratCast]
      exact hv
  rw [tangentSign,rationalSign_eq_oddSign]
  exact oddSign_one_of_left_square q _ _ _ _ hc

#print axioms tangentSign_positive_p
#print axioms tangentSign_positive_b_split

end FourCorner.HasseOddSourceRows
