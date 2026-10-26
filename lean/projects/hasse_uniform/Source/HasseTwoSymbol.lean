import HasseSignAlgebra
import HasseInertSupport

namespace FourCorner.HasseTwoSymbol

open HilbertArithmeticHigh11 HilbertWellDefinedHigh11 HasseSignAlgebra

/-- Exact odd-prime sign of the literal rational symbol (2,r). -/
theorem rationalSign_two_odd (q : OddPrime) (r : ℚ) (hr : r ≠ 0) :
    rationalSign 2 r (by norm_num) hr q.val=
      if IsSquare (2 : ZMod q.val) then 1 else bitSign (padicValRat q.val r : ZMod 2) := by
  classical
  let ys := primePresentation r hr
  have hform : rationalSign 2 r (by norm_num) hr q.val=
      (legendreSym q.val 2)^(HilbertOddFormulaHigh11.order q ys) := by
    rw [rationalSign_eq_presentation 2 r (by norm_num) hr [Atom.two] ys 1 (squareScale r hr)
      one_ne_zero (squareScale_spec r hr).1 (by norm_num [evalPresentation,value])
      (squareScale_spec r hr).2 q.val,
      HilbertOddFormulaHigh11.presentation_odd_formula]
    simp [HilbertOddFormulaHigh11.order,HilbertOddFormulaHigh11.unit,
      HilbertOddFormulaHigh11.atomOrder,HilbertOddFormulaHigh11.atomUnit,
      HilbertOddFormulaHigh11.formula]
  have hval : (padicValRat q.val r : ZMod 2)=(HilbertOddFormulaHigh11.order q ys : ZMod 2) := by
    rw [HilbertOddFormulaHigh11.rational_presentation_valuation q ys (squareScale r hr) r
      (squareScale_spec r hr).1 (squareScale_spec r hr).2]
    push_cast
    simp only [show (2 : ZMod 2)=0 by decide,zero_mul,add_zero]
  have htwo : (2 : ZMod q.val) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hh
    exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
  by_cases hsq : IsSquare (2 : ZMod q.val)
  · rw [hform,(legendreSym.eq_one_iff q.val (by simpa using htwo)).mpr (by simpa using hsq),one_pow,if_pos hsq]
  · rw [hform,(legendreSym.eq_neg_one_iff q.val).mpr (by simpa using hsq),if_neg hsq,hval]
    simp only [bitSign,ZMod.val_natCast]
    exact neg_one_pow_eq_pow_mod_two _

theorem rationalSign_two_real (r : ℚ) (hr : r ≠ 0) : rationalSign 2 r (by norm_num) hr 0=1 := by
  rw [HasseHilbertArithmetic.rationalSign_real]
  norm_num

#print axioms rationalSign_two_odd
#print axioms rationalSign_two_real

end FourCorner.HasseTwoSymbol
