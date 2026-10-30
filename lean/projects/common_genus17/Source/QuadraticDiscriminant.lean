import UnitDiscriminantClosure
import Mathlib.FieldTheory.KummerPolynomial

noncomputable section
open Polynomial
namespace FourCorner.QuadraticDiscriminant
variable {F E : Type*} [Field F] [Field E] [CharZero F] [Algebra F E]

theorem minpoly_eq (B : PowerBasis F E) (a : F) (ha : ¬ IsSquare a)
    (hz : B.gen^2 = algebraMap F E a) :
    minpoly F B.gen = X^2-C a := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro c hc
    exact ha ⟨c,by simpa only [pow_two] using hc.symm⟩
  · simpa only [map_sub,map_pow,aeval_X,aeval_C,sub_eq_zero] using hz
  · exact monic_X_pow_sub_C a (by decide)

/-- The actual power-basis discriminant of the nonsquare quadratic extension
is 4a; this is the denominator/unit calculation used by the local lifting. -/
theorem discr_eq (B : PowerBasis F E) (hdim : B.dim = 2) (a : F)
    (ha : ¬ IsSquare a) (hz : B.gen^2 = algebraMap F E a) :
    Algebra.discr F B.basis = 4*a := by
  letI : FiniteDimensional F E := B.finite
  have hmin := minpoly_eq B a ha hz
  have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly B
  have hn : Module.finrank F E = 2 := B.finrank.trans hdim
  have hnorm' : Algebra.norm F B.gen = -a := by
    simpa [hmin,hdim] using hnorm
  have heval : aeval B.gen (X^2-C a).derivative =
      algebraMap F E (2 : F)*B.gen := by
    simp only [derivative_sub,derivative_X_sq,derivative_C,sub_zero,map_mul,aeval_C,aeval_X]
  rw [Algebra.discr_powerBasis_eq_norm F B,hn,hmin,heval,map_mul,
    Algebra.norm_algebraMap,hn,hnorm']
  norm_num

end FourCorner.QuadraticDiscriminant
#print axioms FourCorner.QuadraticDiscriminant.discr_eq
