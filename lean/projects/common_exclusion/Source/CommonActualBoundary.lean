import CommonFieldCoordinates
import CommonRationalPlace

noncomputable section
namespace FourCorner.CommonLiteralField
open AlgebraicCurve

/-- Every genuine rational place of the literal four-root function field
lies in the finite ell chart. In particular no place above infinity is lost. -/
theorem ell_regular_at_rational_place (t : ℚ) (ht : 1 < t)
    (w : Place ℚ (field ℚ t)) (hw : w.IsRational) :
    ell ℚ t ∈ w.toValuationSubring :=
  CommonRationalPlace.ell_mem_of_rational w hw t ht (ell ℚ t) (root ℚ t 2)
    (ell_ne_zero ℚ t) (by simpa only [eq_ratCast] using sqM ℚ t)

/-- The residue of ell at every actual rational place avoids all five
finite omitted values. Together with the preceding theorem this excludes
all six boundary fibres in the function-field place model. -/
theorem rational_place_avoids_finite_boundary (t : ℚ) (ht : 1 < t)
    (w : Place ℚ (field ℚ t)) (hw : w.IsRational) :
    CommonRationalPlace.rationalEval w hw
      ⟨ell ℚ t,ell_regular_at_rational_place t ht w hw⟩ ∉
      ({0,t-1,t+1,-(t-1),-(t+1)} : Finset ℚ) :=
  CommonRationalPlace.finite_boundary_excluded w hw t ht (ell ℚ t)
    (root ℚ t 0) (root ℚ t 1) (root ℚ t 2) (root ℚ t 3)
    (ell_ne_zero ℚ t) (by simpa only [eq_ratCast] using sqP ℚ t)
    (by simpa only [eq_ratCast] using sqC ℚ t) (by simpa only [eq_ratCast] using sqM ℚ t)
    (by simpa only [eq_ratCast] using sqB ℚ t)
    (ell_regular_at_rational_place t ht w hw)

#print axioms ell_regular_at_rational_place
#print axioms rational_place_avoids_finite_boundary
end FourCorner.CommonLiteralField
