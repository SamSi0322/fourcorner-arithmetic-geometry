import ThetaDCanonicalInfinityDivisor

namespace FourCorner.ThetaDHyperplaneLocalOrders
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDExactChartTransitions ThetaDChartPlaceRegularity ThetaDProjectiveInfinityCover
open SmoothProperClosedPointPlaces ThetaDActualDifferential ThetaDifferentialChartIdentity
open ThetaRegularFunctionDifferential ThetaDGlobalCanonicalCandidate ThetaDInfinityLocalParameter
open ThetaDFourInfinityPlaces ThetaDCanonicalInfinityDivisor
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
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

/-- Exact support comparison with ALL original-geometric closed points,
not only the four displayed point morphisms. -/
theorem infinityPlaces_iff (p : closedPoints geometricD) :
    placeOfClosedPoint toBase p∈infinityPlaces ↔ p.val∉geoU 2 := by
  constructor
  · intro hw
    obtain ⟨a,ha⟩ := (mem_infinityPlaces _).mp hw
    have he : closedPoint a=p := placeOfClosedPoint_injective toBase
      ((place_eq_closedPoint a).symm.trans ha)
    rw [←he]
    exact closedPoint_at_infinity a
  · intro hp
    have hh := infinity_order_positive p hp
    by_contra hn
    rw [all_orders_exact,if_neg hn] at hh
    omega

 theorem infinity_order_one (p : closedPoints geometricD) (hp : p.val∉geoU 2) :
    (placeOfClosedPoint toBase p).ordDifferential omega=1 := by
  rw [all_orders_exact,if_pos ((infinityPlaces_iff p).mpr hp)]

 theorem finite_order_zero (p : closedPoints geometricD) (hp : p.val∈geoU 2) :
    (placeOfClosedPoint toBase p).ordDifferential omega=0 := by
  rw [all_orders_exact,if_neg (by intro h;exact (infinityPlaces_iff p).mp h hp)]

/-- The TRUE local equation v=Z/X has order exactly one at EVERY actual
infinity point. It is derived from canonical degree/order and native local
differential regularity, not assumed to be a uniformizer. -/
theorem local_Z_over_X_order_one (p : closedPoints geometricD) (hp : p.val∉geoU 2) :
    (placeOfClosedPoint toBase p).ord v=1 := by
  let w := placeOfClosedPoint toBase p
  let A := w.toValuationSubring
  let hpx := infinity_in_X p.val hp
  have hvr : v∈A := coordinate_regular_at_chart 0 p hpx 1
  have hv : v≠0 := by rw [XZ_transition.2];exact inv_ne_zero x_ne_zero
  have hvn : (⟨v,hvr⟩ : A)≠0 := by intro h;exact hv (congrArg Subtype.val h)
  have hvp := (Place.mem_maximalIdeal_iff_ord_pos' hvn).mp (infinity_v_mem_maximal p hp)
  change 0<w.ord v at hvp
  let eta : Ω[field⁄K] := (-(Gu u v)⁻¹) • KaehlerDifferential.D K field v
  have he : omega=v • eta := by
    rw [omega_on_X_chart]
    dsimp only [eta]
    rw [smul_smul]
    congr 1
    ring
  have her : coefficient w eta∈A := by
    dsimp only [eta]
    rw [map_smul]
    exact A.toSubring.mul_mem (A.toSubring.neg_mem (Gu_unit_at_infinity p hp).2)
      (coefficient_D_mem w v hvr)
  have hen : coefficient w eta≠0 := by
    intro hz
    apply coefficient_nonzero w
    rw [he,map_smul,hz,smul_zero]
  have heord : w.ordDifferential omega=w.ord v+w.ordDifferential eta := by
    rw [he]
    exact w.ordDifferential_smul hv hen
  have hη : 0≤w.ordDifferential eta := w.ord_nonneg_of_mem her
  have hw1 : w.ordDifferential omega=1 := infinity_order_one p hp
  change w.ord v=1
  omega

/-- Exact canonical/local-section order comparison on the TRUE two-chart
plane cover: Z/Z=1 on Z≠0, and Z/X=v at infinity. This does not redefine
the native Picard or Cartier object; it supplies their genuine local orders. -/
theorem canonical_matches_Z_local_equations (p : closedPoints geometricD) :
    (canonicalDivisorOf omega_ne_zero) (placeOfClosedPoint toBase p)=
      if p.val∈geoU 2 then (placeOfClosedPoint toBase p).ord 1
      else (placeOfClosedPoint toBase p).ord v := by
  rw [canonicalDivisorOf_apply]
  by_cases hp : p.val∈geoU 2
  · rw [if_pos hp,finite_order_zero p hp,Place.ord_one]
  · rw [if_neg hp,infinity_order_one p hp,local_Z_over_X_order_one p hp]

#print axioms infinityPlaces_iff
#print axioms infinity_order_one
#print axioms finite_order_zero
#print axioms local_Z_over_X_order_one
#print axioms canonical_matches_Z_local_equations
end
end FourCorner.ThetaDHyperplaneLocalOrders
