import ThetaDGlobalCanonicalCandidate

namespace FourCorner.ThetaDPlaneRegularForms
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDExactChartTransitions ThetaDChartPlaceRegularity ThetaDProjectiveInfinityCover
open SmoothProperClosedPointPlaces ThetaDActualDifferential ThetaDifferentialChartIdentity
open ThetaRegularFunctionDifferential ThetaDGlobalCanonicalCandidate
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

 theorem xomega_coefficient_regular (w : Place K field) :
    coefficient w (x • omega)∈w.toValuationSubring := by
  obtain ⟨p,hp⟩ := (closedPointPlaceEquiv toBase).surjective w
  change placeOfClosedPoint toBase p=w at hp
  rw [←hp]
  let W := (placeOfClosedPoint toBase p).toValuationSubring.toSubring
  by_cases hf : p.val∈geoU 2
  · rw [map_smul]
    exact W.mul_mem (coordinate_regular_at_chart 2 p hf 0)
      (all_coefficients_regular _)
  · rw [xomega_on_X_chart,map_smul]
    change (-1*(Gu u v)⁻¹)*coefficient (placeOfClosedPoint toBase p)
      (KaehlerDifferential.D K field v)∈W
    exact W.mul_mem (W.mul_mem (W.neg_mem W.one_mem) (Gu_unit_at_infinity p hf).2)
      (coefficient_D_mem _ v (coordinate_regular_at_chart 0 p (infinity_in_X p.val hf) 1))

 theorem yomega_coefficient_regular (w : Place K field) :
    coefficient w (y • omega)∈w.toValuationSubring := by
  obtain ⟨p,hp⟩ := (closedPointPlaceEquiv toBase).surjective w
  change placeOfClosedPoint toBase p=w at hp
  rw [←hp]
  let W := (placeOfClosedPoint toBase p).toValuationSubring.toSubring
  by_cases hf : p.val∈geoU 2
  · rw [map_smul]
    exact W.mul_mem (coordinate_regular_at_chart 2 p hf 1)
      (all_coefficients_regular _)
  · rw [yomega_on_X_chart,map_smul]
    change (-u*(Gu u v)⁻¹)*coefficient (placeOfClosedPoint toBase p)
      (KaehlerDifferential.D K field v)∈W
    exact W.mul_mem (W.mul_mem
      (W.neg_mem (coordinate_regular_at_chart 0 p (infinity_in_X p.val hf) 0))
      (Gu_unit_at_infinity p hf).2)
      (coefficient_D_mem _ v (coordinate_regular_at_chart 0 p (infinity_in_X p.val hf) 1))

 theorem xomega_regular : x • omega∈regularDifferentials K field := by
  intro w
  exact ⟨coefficient w (x • omega),xomega_coefficient_regular w,
    (w.differentialCoeff_smul_dCoord _).symm⟩

 theorem yomega_regular : y • omega∈regularDifferentials K field := by
  intro w
  exact ⟨coefficient w (y • omega),yomega_coefficient_regular w,
    (w.differentialCoeff_smul_dCoord _).symm⟩

/-- The actual native vector space of regular differentials on the same
original geometric curve is finite and has dimension three. -/
theorem regular_dimension_three :
    Module.Finite K (regularDifferentials K field) ∧
      Module.finrank K (regularDifferentials K field)=3 := by
  obtain ⟨hf,hg⟩ := finite_and_finrank_regularDifferentials_eq_genus (K:=K) (F:=field)
  exact ⟨hf,hg.trans ThetaDNativeSections.divisor_genus_three⟩

#print axioms xomega_regular
#print axioms yomega_regular
#print axioms regular_dimension_three
end
end FourCorner.ThetaDPlaneRegularForms
