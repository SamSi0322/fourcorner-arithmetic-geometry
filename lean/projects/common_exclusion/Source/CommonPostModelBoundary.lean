import CommonPostBoundaryPlaces
import CommonPostFiniteP1

noncomputable section
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.CommonPostModelBoundary
open CommonPostGeometricGenus CommonSchemeModel CommonPostPointResidue CommonPostBoundaryPlaces

/-- Every rational point of the same actual D_t model has a precise field place
whose restriction avoids all six literal ell-boundary places. -/
theorem actual_model_point_avoids_boundary (t : ℚ) (ht : 1 < t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := modelFieldAlgebra t
    ∀ p : Spec (.of ℚ) ⟶ CommonPostFiniteP1.commonCurve t h0 h1 hm,
      restrictToLine (pointPlace (model t h0 h1 hm) p) ∉ CommonFourPlaceOrders.support t := by
  letI := modelFieldAlgebra t
  intro p
  exact rational_point_avoids_forAlgebra t ht (modelFieldAlgebra t) (model t h0 h1 hm) p

end FourCorner.CommonPostModelBoundary
#print axioms FourCorner.CommonPostModelBoundary.actual_model_point_avoids_boundary
