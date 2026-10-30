import ThetaCoverClassPortable.ThetaDNativeProjRatios

namespace FourCorner.ThetaDProjectiveInfinityCover
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections ThetaDChartNaturality ThetaDNativeProjRatios
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev homogeneousRing := ThetaQuotientChart.Q (targetEquation ℚ) (target_homogeneous ℚ)

 theorem homogeneous_relation :
    9801*(hcoordinate 0^4+hcoordinate 1^4)+19598*(hcoordinate 0^2*hcoordinate 1^2)-
      39592*((hcoordinate 0^2+hcoordinate 1^2)*hcoordinate 2^2)+39984*hcoordinate 2^4=0 := by
  have h : ThetaQuotientChart.quotientMap (targetEquation ℚ) (target_homogeneous ℚ)
      (targetEquation ℚ 0)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)
  simpa only [targetEquation,targetPolynomial,map_add,map_sub,map_mul,map_pow,map_ofNat] using h

/-- An actual point of original D cannot have both X=0 and Z=0. This uses
the homogeneous prime ideal of that point and the original quartic equation. -/
theorem X_or_Z (p : D ℚ) : p∈B 0 ∨ p∈B 2 := by
  by_contra hn
  push_neg at hn
  have hx : hcoordinate 0∈p.asHomogeneousIdeal := not_not.mp hn.1
  have hz : hcoordinate 2∈p.asHomogeneousIdeal := not_not.mp hn.2
  let I := p.asHomogeneousIdeal.toIdeal
  let S := homogeneousRing ⧸ I
  let f : homogeneousRing →+* S := Ideal.Quotient.mk I
  have hfx : f (hcoordinate 0)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hfz : f (hcoordinate 2)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hr := congrArg f homogeneous_relation
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero,hfx,hfz,zero_pow,
    zero_add,add_zero,zero_mul,mul_zero,sub_zero] at hr
  norm_num at hr
  have hc : (9801:S)≠0 := by
    have hq : (9801:ℚ)≠0 := by norm_num
    simpa only [map_ofNat,map_zero] using (algebraMap ℚ S).injective.ne hq
  have hy0 : f (hcoordinate 1)=0 := hr.resolve_left hc
  have hy : hcoordinate 1∈I := Ideal.Quotient.eq_zero_iff_mem.mp hy0
  apply p.not_irrelevant_le
  intro a ha
  have hspan : Ideal.span (Set.range (ThetaProjectiveModel.coordinate (targetEquation ℚ) (target_homogeneous ℚ))) ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  exact hspan ((irrelevant_span (targetEquation ℚ) (target_homogeneous ℚ)) ha)

 theorem original_XZ_cover : B 0 ⊔ B 2=⊤ := by
  ext p
  constructor
  · intro _;trivial
  · intro _;exact X_or_Z p

/-- The SAME actual categorical geometric pullback has the genuine two-chart
cover X≠0 or Z≠0; every point at infinity lies in the X-chart. -/
theorem geometric_XZ_cover : geoU 0 ⊔ geoU 2=⊤ := by
  rw [geoU,geoU, U_eq_basic 0,U_eq_basic 2]
  change pullback.fst (dToBase ℚ) qb ⁻¹ᵁ (B 0 ⊔ B 2)=⊤
  rw [original_XZ_cover]
  rfl

 theorem infinity_in_X (p : geometricD) (hp : p∉geoU 2) : p∈geoU 0 := by
  have hh : p∈geoU 0 ⊔ geoU 2 := by rw [geometric_XZ_cover];trivial
  exact hh.resolve_right hp

#print axioms homogeneous_relation
#print axioms X_or_Z
#print axioms geometric_XZ_cover
end
end FourCorner.ThetaDProjectiveInfinityCover
