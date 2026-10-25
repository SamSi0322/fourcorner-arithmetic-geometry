import geometry.GeometricFractionField
import geometry.OppositeAffineModel

noncomputable section
open scoped TensorProduct
namespace FourCorner.OppositeAffineModel
open OppositeCoordinateAlgebra

/-- Geometric integrality of the genuine opposite function field: extending
constants to any field preserves the domain property. -/
theorem rational_functionField_all_extensions_domain (L : Type*) [Field L] [Algebra ℚ L]
    (mu nu : ℚ) (hnu : nu ≠ 0) (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    IsDomain (L ⊗[ℚ] functionField mu nu) := by
  let := rational_coordinateRing_isDomain mu nu hnu hpos hlt
  let := rational_coordinateRing_isFractionRing mu nu hnu hpos hlt
  let := rational_all_field_extensions_integral L mu nu hnu hpos hlt
  exact GeometricFractionField.isDomain_baseChange_fractionRing ℚ (ring mu nu)
    (functionField mu nu) L

#print axioms rational_functionField_all_extensions_domain
end FourCorner.OppositeAffineModel
