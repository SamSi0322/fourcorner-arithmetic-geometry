import ThetaCoverClassPortable.ThetaDInfinityLocalParameter

namespace FourCorner.ThetaDGlobalCanonicalCandidate
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDExactChartTransitions ThetaDCoordinateBasicOpens ThetaDChartPlaceRegularity
open ThetaDProjectiveInfinityCover SmoothProperClosedPointPlaces ThetaDInfinityLocalParameter
open ThetaDActualDifferential ThetaDifferentialChartIdentity ThetaRegularFunctionDifferential
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
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

 theorem infinity_derivative_nonzero {E : Type*} [Field E] [CharZero E] (a : E)
    (h : 9801*a^4+19598*a^2+9801=0) : a*(39196+39204*a^2)≠0 := by
  intro hd
  have hu : (1:E)=0 := by
    linear_combination ((1/9801)-(9799/39200)*a^2)*h+
      ((95981201/1536796800)*a+(9799/156800)*a^3)*hd
  exact one_ne_zero hu

/-- The ACTUAL X-chart partial derivative is a unit at EVERY actual point
at infinity; no local-unit hypothesis is imposed. -/
theorem Gu_unit_at_infinity (p : closedPoints geometricD) (hp : p.val∉geoU 2) :
    Gu u v≠0 ∧ (Gu u v)⁻¹∈(placeOfClosedPoint toBase p).toValuationSubring := by
  let w := placeOfClosedPoint toBase p
  let A := w.toValuationSubring
  let hpx := infinity_in_X p.val hp
  let a : A := ⟨u,coordinate_regular_at_chart 0 p hpx 0⟩
  let b : A := ⟨v,coordinate_regular_at_chart 0 p hpx 1⟩
  have he : 9801*a^4+19598*a^2+39984*b^4-b^2*(39592*a^2+39592)+9801=0 := by
    apply Subtype.val_injective
    exact field_relation 0 0
  let r := IsLocalRing.residue A
  have hb : r b=0 := (IsLocalRing.residue_eq_zero_iff b).mpr (infinity_v_mem_maximal p hp)
  have hr := congrArg r he
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero] at hr
  have hr0 : 9801*(r a)^4+19598*(r a)^2+9801=0 := by simpa [hb] using hr
  letI : CharZero w.ResidueField := charZero_of_injective_algebraMap (algebraMap K w.ResidueField).injective
  have hgn := infinity_derivative_nonzero (r a) hr0
  let g : A := a*(39196+39204*a^2-79184*b^2)
  have hb' : IsLocalRing.residue A b=0 := hb
  have heq : IsLocalRing.residue A g=(r a)*(39196+39204*(r a)^2) := by
    simp only [g,map_mul,map_add,map_sub,map_pow,map_ofNat,hb']
    ring
  have hg : IsUnit g := (IsLocalRing.residue_ne_zero_iff_isUnit g).mp (by
    rw [heq]
    exact hgn)
  exact ⟨fun hz=>hg.ne_zero (Subtype.ext hz),ThetaDFiniteDifferential.inv_mem_of_isUnit hg⟩

/-- At every actual point at infinity the actual differential coefficient
is in the maximal ideal, because omega=-v dv/F_u and v=Z/X truly vanishes. -/
theorem infinity_coefficient_maximal (p : closedPoints geometricD) (hp : p.val∉geoU 2) :
    ∃c : (placeOfClosedPoint toBase p).toValuationSubring,
      (c:field)=coefficient (placeOfClosedPoint toBase p) omega ∧
        c∈IsLocalRing.maximalIdeal (placeOfClosedPoint toBase p).toValuationSubring := by
  let w := placeOfClosedPoint toBase p
  let A := w.toValuationSubring
  let hpx := infinity_in_X p.val hp
  let b : A := ⟨v,coordinate_regular_at_chart 0 p hpx 1⟩
  let g : A := ⟨(Gu u v)⁻¹,(Gu_unit_at_infinity p hp).2⟩
  let d : A := ⟨coefficient w (KaehlerDifferential.D K field v),
    coefficient_D_mem w v (coordinate_regular_at_chart 0 p hpx 1)⟩
  refine ⟨-b*g*d,?_,?_⟩
  · change -v*(Gu u v)⁻¹*coefficient w (KaehlerDifferential.D K field v)=coefficient w omega
    rw [omega_on_X_chart,map_smul]
    rfl
  · exact (IsLocalRing.maximalIdeal A).mul_mem_right d
      ((IsLocalRing.maximalIdeal A).mul_mem_right g
        ((IsLocalRing.maximalIdeal A).neg_mem (infinity_v_mem_maximal p hp)))

 theorem coefficient_nonzero (w : Place K field) : coefficient w omega≠0 := by
  intro hz
  have hh := w.differentialCoeff_smul_dCoord omega
  change coefficient w omega • w.dCoord=omega at hh
  rw [hz,zero_smul] at hh
  exact omega_ne_zero hh.symm

 theorem infinity_order_positive (p : closedPoints geometricD) (hp : p.val∉geoU 2) :
    0<(placeOfClosedPoint toBase p).ordDifferential omega := by
  obtain ⟨c,hc,hm⟩ := infinity_coefficient_maximal p hp
  have hn : c≠0 := by intro hz;exact coefficient_nonzero _ (hc.symm.trans (congrArg Subtype.val hz))
  have hh := (Place.mem_maximalIdeal_iff_ord_pos' hn).mp hm
  change 0<(placeOfClosedPoint toBase p).ord (c:field) at hh
  rw [hc] at hh
  exact hh

/-- Regularity at ALL native places of the SAME original geometric D,
including every place at infinity. -/
theorem all_coefficients_regular (w : Place K field) :
    coefficient w omega∈w.toValuationSubring := by
  obtain ⟨p,hp⟩ := (closedPointPlaceEquiv toBase).surjective w
  change placeOfClosedPoint toBase p=w at hp
  rw [←hp]
  by_cases hf : p.val∈geoU 2
  · exact omega_regular_at_finite_closed_point p hf
  · obtain ⟨c,hc,_⟩ := infinity_coefficient_maximal p hf
    rw [←hc]
    exact c.property

 theorem omega_regular : omega∈regularDifferentials K field := by
  intro w
  exact ⟨coefficient w omega,all_coefficients_regular w,(w.differentialCoeff_smul_dCoord omega).symm⟩

 theorem all_orders_nonnegative (w : Place K field) : 0≤w.ordDifferential omega :=
  w.ord_nonneg_of_mem (all_coefficients_regular w)

 theorem canonical_candidate_effective : (0 : Divisor K field)≤canonicalDivisorOf omega_ne_zero := by
  intro w
  rw [canonicalDivisorOf_apply]
  exact all_orders_nonnegative w

 theorem canonical_candidate_degree_four : Divisor.degree (canonicalDivisorOf omega_ne_zero)=4 :=
  ThetaDNativeSections.canonical_degree_four omega_ne_zero

#print axioms Gu_unit_at_infinity
#print axioms infinity_order_positive
#print axioms omega_regular
#print axioms canonical_candidate_effective
#print axioms canonical_candidate_degree_four
end
end FourCorner.ThetaDGlobalCanonicalCandidate
