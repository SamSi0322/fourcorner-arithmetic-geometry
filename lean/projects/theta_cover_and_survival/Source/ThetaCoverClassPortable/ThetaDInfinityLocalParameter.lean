import ThetaCoverClassPortable.ThetaDCoordinateBasicOpens

namespace FourCorner.ThetaDInfinityLocalParameter
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDExactChartTransitions ThetaDCoordinateBasicOpens ThetaDChartPlaceRegularity
open ThetaDProjectiveInfinityCover SmoothProperClosedPointPlaces
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance (j : Fin 3) : Nonempty (geoU j) := geoU_nonempty j

/-- The ACTUAL X-chart section v=Z/X belongs to the maximal ideal at EVERY
actual closed point at infinity. The proof uses its true nonvanishing open,
the original projective equation, and the actual point-place stalk comparison. -/
theorem infinity_v_mem_maximal (p : closedPoints geometricD) (hp : p.val∉geoU 2) :
    (⟨v,coordinate_regular_at_chart 0 p (infinity_in_X p.val hp) 1⟩ :
      (placeOfClosedPoint toBase p).toValuationSubring)∈
        IsLocalRing.maximalIdeal (placeOfClosedPoint toBase p).toValuationSubring := by
  let hpx : p.val∈geoU 0 := infinity_in_X p.val hp
  let z := geometricD.presheaf.germ (geoU 0) p.val hpx (coordinateSection 0 1)
  have hn : ¬IsUnit z := by
    intro hu
    have hh : p.val∈geometricD.basicOpen (coordinateSection 0 1) :=
      (geometricD.mem_basicOpen _ p.val hpx).mpr hu
    rw [X_v_basicOpen] at hh
    exact hp hh.2
  let e := stalkValuationEquiv toBase p
  have he : ((e z : (placeOfClosedPoint toBase p).toValuationSubring):field)=v := by
    rw [stalkValuationEquiv_coe]
    exact geometricD.algebraMap_germ_eq_germToFunctionField hpx (coordinateSection 0 1)
  have he' : e z=(⟨v,coordinate_regular_at_chart 0 p (infinity_in_X p.val hp) 1⟩ :
      (placeOfClosedPoint toBase p).toValuationSubring) := Subtype.ext he
  rw [←he',IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit (e z)
  intro hu
  exact hn (IsUnit.of_leftInverse e.symm.toRingHom e.left_inv hu)

#print axioms infinity_v_mem_maximal
end
end FourCorner.ThetaDInfinityLocalParameter
