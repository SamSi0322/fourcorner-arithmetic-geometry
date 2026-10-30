import ThetaCoverClassPortable.ThetaDExactChartTransitions

namespace FourCorner.ThetaDCoordinateBasicOpens
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
open ThetaDChartNaturality ThetaDNativeProjRatios ThetaDNativeProjSections ThetaDSectionComparison
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.propDecidable MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

 theorem section_coordinate_stalk (j : Fin 3) (a : Fin 2) (p : D ℚ) (hp : p∈B j) :
    Proj.stalkIso' G p ((D ℚ).presheaf.germ (B j) p hp
      (sections j (Ideal.Quotient.mk _ (X a))))=
    HomogeneousLocalization.mk ⟨1,⟨hcoordinate (ThetaAmbientChart.insert 2 j a),coordinate_degree _ _ _⟩,
      ⟨hcoordinate j,coordinate_degree _ _ _⟩,hp⟩ := by
  erw [Proj.stalkIso'_germ]
  dsimp only [sections,RingHom.comp_apply]
  rw [ThetaQuotientChart.chartInverse_mk]
  simp only [ThetaAmbientChart.ambientInverse,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_X]
  change HomogeneousLocalization.mapId G _
    (HomogeneousLocalization.Away.map (ThetaQuotientChart.quotientMap (targetEquation ℚ) (target_homogeneous ℚ)) _
      (Slot02HighProjSpace.ratio ℚ 2 j (ThetaAmbientChart.insert 2 j a)))=_
  rw [Slot02HighProjSpace.ratio,HomogeneousLocalization.Away.map_mk]
  simp only [HomogeneousLocalization.Away.mk,HomogeneousLocalization.mapId,HomogeneousLocalization.map_mk,pow_one]
  rfl

/-- The nonvanishing open of a genuine homogeneous-ratio section is exactly
intersection of the two original projective standard opens. -/
theorem native_coordinate_basicOpen (j : Fin 3) (a : Fin 2) :
    (D ℚ).basicOpen (sections j (Ideal.Quotient.mk _ (X a)))=
      B j ⊓ B (ThetaAmbientChart.insert 2 j a) := by
  ext p
  change (p∈(D ℚ).basicOpen (sections j (Ideal.Quotient.mk _ (X a)))) ↔
    p∈B j ∧ p∈B (ThetaAmbientChart.insert 2 j a)
  by_cases hp : p∈B j
  · rw [(D ℚ).mem_basicOpen _ p hp]
    rw [←isUnit_map_of_leftInverse (f:=(Proj.stalkIso' G p).toRingHom)
      (Proj.stalkIso' G p).symm.toRingHom (Proj.stalkIso' G p).left_inv]
    erw [section_coordinate_stalk j a p hp]
    rw [←HomogeneousLocalization.isUnit_iff_isUnit_val]
    rw [HomogeneousLocalization.val_mk,Localization.mk_eq_mk',IsLocalization.AtPrime.isUnit_mk'_iff]
    exact (and_iff_right hp).symm
  · have hh := (D ℚ).basicOpen_le (sections j (Ideal.Quotient.mk _ (X a)))
    constructor
    · intro h;exact False.elim (hp (hh h))
    · intro h;exact False.elim (hp h.1)

 theorem original_section_value (j : Fin 3) (r : chartRing j) :
    (sectionsRingEquiv j).symm r=
      ((D ℚ).presheaf.map (eqToHom (U_eq_basic j)).op).hom (sections j r) := by
  apply (sectionsRingEquiv j).injective
  rw [RingEquiv.apply_symm_apply]
  exact (congrArg (fun f : CommRingCat.of (chartRing j) ⟶ CommRingCat.of (chartRing j) => f.hom r)
    (sections_comparison_hom j)).symm

def coordinateSection (j : Fin 3) (a : Fin 2) : Γ(geometricD,geoU j) :=
  actualChartEquiv j (1 ⊗ₜ[ℚ] (Ideal.Quotient.mk _ (X a)))

/-- The ACTUAL geometric coordinate sections have their correct geometric
nonvanishing opens, after the TRUE categorical base change. -/
theorem coordinateSection_basicOpen (j : Fin 3) (a : Fin 2) :
    geometricD.basicOpen (coordinateSection j a)=
      geoU j ⊓ geoU (ThetaAmbientChart.insert 2 j a) := by
  rw [coordinateSection,actualChartEquiv_one_tmul,←Scheme.preimage_basicOpen]
  change pullback.fst (dToBase ℚ) qb ⁻¹ᵁ
    (D ℚ).basicOpen ((sectionsRingEquiv j).symm (Ideal.Quotient.mk _ (X a)))=_
  rw [original_section_value,Scheme.basicOpen_res_eq,native_coordinate_basicOpen]
  rw [geoU,geoU,U_eq_basic,U_eq_basic]
  rfl

 theorem X_v_basicOpen :
    geometricD.basicOpen (coordinateSection 0 1)=geoU 0 ⊓ geoU 2 := by
  exact coordinateSection_basicOpen 0 1

#print axioms section_coordinate_stalk
#print axioms native_coordinate_basicOpen
#print axioms coordinateSection_basicOpen
#print axioms X_v_basicOpen
end
end FourCorner.ThetaDCoordinateBasicOpens
