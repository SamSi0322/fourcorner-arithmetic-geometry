import ThetaDFiniteDifferential
import SmoothProperClosedPointPlaces

namespace FourCorner.ThetaDChartPlaceRegularity
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDActualDifferential ThetaRegularFunctionDifferential SmoothProperClosedPointPlaces
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance (j : Fin 3) : Nonempty (geoU j) := geoU_nonempty j

/-- Every ACTUAL affine section is regular in the place obtained from
its actual closed-point stalk, inside the SAME native function field. -/
theorem chart_section_mem (j : Fin 3) (p : closedPoints geometricD)
    (hp : p.val∈geoU j) (s : Γ(geometricD,geoU j)) :
    (geometricD.germToFunctionField (geoU j)) s∈
      (placeOfClosedPoint toBase p).toValuationSubring := by
  change _∈(placeOfClosedPoint toBase p).toValuationSubring.toSubring
  rw [←range_stalk toBase p]
  exact ⟨geometricD.presheaf.germ (geoU j) p.val hp s,
    geometricD.algebraMap_germ_eq_germToFunctionField hp s⟩

 theorem coordinate_regular_at_chart (j : Fin 3) (p : closedPoints geometricD)
    (hp : p.val∈geoU j) (a : Fin 2) :
    coordinate j a∈(placeOfClosedPoint toBase p).toValuationSubring :=
  chart_section_mem j p hp
    (actualChartEquiv j (1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (MvPolynomial.X a))))

/-- The actual nonzero dx/F_y is regular at EVERY closed point of the
original geometric quartic in its true Z≠0 chart. No unit/gradient premise
is imposed on these points. -/
theorem omega_regular_at_finite_closed_point (p : closedPoints geometricD)
    (hp : p.val∈geoU 2) :
    coefficient (placeOfClosedPoint toBase p) omega∈
      (placeOfClosedPoint toBase p).toValuationSubring :=
  ThetaDFiniteDifferential.omega_regular_where_coordinates_regular _
    (coordinate_regular_at_chart 2 p hp 0) (coordinate_regular_at_chart 2 p hp 1)

/-- This statement quantifies over ALL native places whose actual centre
is in the original finite chart, using the proved point-place bijection. -/
theorem omega_regular_at_finite_place (w : Place K field)
    (hw : ((closedPointPlaceEquiv toBase).symm w).val∈geoU 2) :
    coefficient w omega∈w.toValuationSubring := by
  have hh := omega_regular_at_finite_closed_point ((closedPointPlaceEquiv toBase).symm w) hw
  simpa only [←closedPointPlaceEquiv_apply,Equiv.apply_symm_apply] using hh

#print axioms chart_section_mem
#print axioms coordinate_regular_at_chart
#print axioms omega_regular_at_finite_closed_point
#print axioms omega_regular_at_finite_place
end
end FourCorner.ThetaDChartPlaceRegularity
