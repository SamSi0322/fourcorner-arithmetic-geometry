import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord

set_option autoImplicit false
noncomputable section
namespace FourCorner.PoleFieldDegree
open AlgebraicCurve

/-- The genuine full pole divisor measures the degree of the ACTUAL simple
function-field extension. Both inequalities are proved, not assumed. -/
theorem degree_eq_finrank_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (f : F) (hf : Transcendental K f)
    [FiniteDimensional (IntermediateField.adjoin K ({f} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F,D v=max 0 (-v.ord f)) :
    Divisor.degree D=(Module.finrank (IntermediateField.adjoin K ({f} : Set F)) F : ℤ) :=
  le_antisymm
    (P2MW.S_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.solution f hf D hD)
    (P2MW.S_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.solution f hf D hD)

#print axioms degree_eq_finrank_adjoin
end FourCorner.PoleFieldDegree
