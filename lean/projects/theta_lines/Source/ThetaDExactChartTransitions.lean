import ThetaDSectionComparison
import ThetaDProjectiveInfinityCover

namespace FourCorner.ThetaDExactChartTransitions
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDChartNaturality ThetaDNativeProjRatios ThetaDNativeProjSections ThetaDSectionComparison
open ThetaNativeFunctionFieldMap ThetaDActualDifferential ThetaDifferentialChartIdentity
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral (D ℚ) := original_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : Surjective qb := qb_surjective
local instance : Surjective (pullback.fst (dToBase ℚ) qb) := inferInstance
local instance (j : Fin 3) : Nonempty (U j) := U_nonempty j
local instance (j : Fin 3) : Nonempty (B j) := basic_nonempty j

/-- The earlier ACTUAL Γ-defined coordinates and the actual native Proj
homogeneous ratios are the SAME elements of the SAME geometric function field. -/
theorem coordinate_eq_native_ratio (j : Fin 3) (a : Fin 2) :
    ThetaDFieldCoordinates.coordinate j a=
      fieldMap (pullback.fst (dToBase ℚ) qb) (ratio j (ThetaAmbientChart.insert 2 j a)) := by
  rw [ThetaDFieldCoordinates.coordinate,chartToField_one_tmul]
  change fieldMap _ ((D ℚ).germToFunctionField (U j)
    ((sectionsRingEquiv j).symm (Ideal.Quotient.mk _ (MvPolynomial.X a))))=_
  rw [original_section_comparison,sections_coordinate_generic]

abbrev u : field := ThetaDFieldCoordinates.coordinate 0 0
abbrev v : field := ThetaDFieldCoordinates.coordinate 0 1
abbrev uY : field := ThetaDFieldCoordinates.coordinate 1 0
abbrev vY : field := ThetaDFieldCoordinates.coordinate 1 1

 theorem XZ_transition : u=y/x ∧ v=x⁻¹ := by
  have h00 := coordinate_eq_native_ratio 0 0
  have h01 := coordinate_eq_native_ratio 0 1
  have h20 := coordinate_eq_native_ratio 2 0
  have h21 := coordinate_eq_native_ratio 2 1
  have i00 : ThetaAmbientChart.insert 2 0 0=1 := rfl
  have i01 : ThetaAmbientChart.insert 2 0 1=2 := rfl
  have i20 : ThetaAmbientChart.insert 2 2 0=0 := rfl
  have i21 : ThetaAmbientChart.insert 2 2 1=1 := rfl
  rw [i00] at h00;rw [i01] at h01;rw [i20] at h20;rw [i21] at h21
  change ThetaDFieldCoordinates.coordinate 0 0=ThetaDFieldCoordinates.coordinate 2 1/ThetaDFieldCoordinates.coordinate 2 0 ∧
    ThetaDFieldCoordinates.coordinate 0 1=(ThetaDFieldCoordinates.coordinate 2 0)⁻¹
  rw [h00,h01,h20,h21]
  constructor
  · rw [transition_XZ.1,map_div₀]
  · rw [transition_XZ.2,map_inv₀]

 theorem YZ_transition : uY=x/y ∧ vY=y⁻¹ := by
  have h10 := coordinate_eq_native_ratio 1 0
  have h11 := coordinate_eq_native_ratio 1 1
  have h20 := coordinate_eq_native_ratio 2 0
  have h21 := coordinate_eq_native_ratio 2 1
  have i10 : ThetaAmbientChart.insert 2 1 0=0 := rfl
  have i11 : ThetaAmbientChart.insert 2 1 1=2 := rfl
  have i20 : ThetaAmbientChart.insert 2 2 0=0 := rfl
  have i21 : ThetaAmbientChart.insert 2 2 1=1 := rfl
  rw [i10] at h10;rw [i11] at h11;rw [i20] at h20;rw [i21] at h21
  change ThetaDFieldCoordinates.coordinate 1 0=ThetaDFieldCoordinates.coordinate 2 0/ThetaDFieldCoordinates.coordinate 2 1 ∧
    ThetaDFieldCoordinates.coordinate 1 1=(ThetaDFieldCoordinates.coordinate 2 1)⁻¹
  rw [h10,h11,h20,h21]
  constructor
  · rw [transition_YZ.1,map_div₀]
  · rw [transition_YZ.2,map_inv₀]

/-- The canonical candidate's exact expression on the ACTUAL X-chart.
These u,v are its real affine sections, not unproved rational substitutions. -/
 theorem omega_on_X_chart :
    omega=(-v/Gu u v) • KaehlerDifferential.D K field v := by
  rw [XZ_transition.1,XZ_transition.2]
  exact actual_omega_transition

 theorem xomega_on_X_chart :
    x • omega=(-1/Gu u v) • KaehlerDifferential.D K field v := by
  rw [XZ_transition.1,XZ_transition.2]
  exact xomega_transition x y x_ne_zero Fy_ne_zero

 theorem yomega_on_X_chart :
    y • omega=(-u/Gu u v) • KaehlerDifferential.D K field v := by
  rw [XZ_transition.1,XZ_transition.2]
  exact yomega_transition x y x_ne_zero Fy_ne_zero

#print axioms coordinate_eq_native_ratio
#print axioms XZ_transition
#print axioms YZ_transition
#print axioms omega_on_X_chart
#print axioms xomega_on_X_chart
#print axioms yomega_on_X_chart
end
end FourCorner.ThetaDExactChartTransitions
