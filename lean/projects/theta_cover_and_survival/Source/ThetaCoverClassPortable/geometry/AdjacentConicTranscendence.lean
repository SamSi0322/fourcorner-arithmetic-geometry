import ThetaCoverClassPortable.geometry.AdjacentConic

/-!
The first coordinate of the nondegenerate adjacent conic is transcendental.
Consequently it defines an injective evaluation map from the polynomial ring.
-/

noncomputable section

namespace FourCorner.AdjacentConic

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- The first chart coordinate is nonconstant, hence transcendental over `K`. -/
theorem u_transcendental (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    Transcendental K (u c) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨a, ha⟩
  have he := (div_eq_iff (denominator_ne_zero c hc)).mp ha
  have hp : C c * ((C c) ^ 2 * X ^ 2 - (C c) ^ 2 + 1) =
      C a * ((C c) ^ 2 * X ^ 2 + (C c) ^ 2 - 1) := by
    apply RatFunc.algebraMap_injective K
    simpa [Chart.u, Chart.denominator, RatFunc.algebraMap_eq_C] using he
  have h2 := congrArg (fun p : K[X] => p.coeff 2) hp
  have h0 := congrArg (fun p : K[X] => p.coeff 0) hp
  norm_num [← map_pow, coeff_one] at h2 h0
  have hac : a = c := (h2.resolve_right hc).symm
  subst a
  have hz : 2 * c * (c ^ 2 - 1) = 0 := by linear_combination -h0
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hc) hA) hz

/-- Polynomial expressions in the first coordinate retain all coefficients. -/
theorem aeval_u_injective (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    Function.Injective (aeval (u c) : K[X] →ₐ[K] RatFunc K) :=
  transcendental_iff_injective.mp (u_transcendental c hc hA)

#print axioms u_transcendental
#print axioms aeval_u_injective

end FourCorner.AdjacentConic
