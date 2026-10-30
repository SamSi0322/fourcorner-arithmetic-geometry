import PadicTranscendental
import Mathlib.RingTheory.Algebraic.Integral

noncomputable section
open Polynomial
namespace FourCorner.TranscendentalParameters
variable {L : Type*} [Field L] [CharZero L]

theorem affine_square {u : L} (hu : Transcendental ℚ u) (a b : ℚ) (hb : b ≠ 0) :
    Transcendental ℚ ((a : L)+(b : L)*u^2) := by
  have hd : (C b*X^2+C a : ℚ[X]).natDegree = 2 := by simp [hb]
  have hn : (C b*X^2+C a : ℚ[X]) ≠ 0 := by
    intro hz
    rw [hz,natDegree_zero] at hd
    norm_num at hd
  have h := hu.aeval (C b*X^2+C a) (by omega)
    (mem_nonZeroDivisors_of_ne_zero (leadingCoeff_ne_zero.mpr hn))
  simpa only [map_add,map_mul,map_pow,aeval_C,aeval_X,eq_ratCast,add_comm] using h

theorem inverse_square {u : L} (hu : Transcendental ℚ u) (b : ℚ) (hb : b ≠ 0) :
    Transcendental ℚ ((b : L)/u^2) := by
  have hi : Transcendental ℚ u⁻¹ := fun h => hu (IsAlgebraic.inv_iff.mp h)
  have h := affine_square hi 0 b hb
  simpa only [Rat.cast_zero,zero_add,inv_pow,div_eq_mul_inv] using h

end FourCorner.TranscendentalParameters
#print axioms FourCorner.TranscendentalParameters.affine_square
#print axioms FourCorner.TranscendentalParameters.inverse_square
