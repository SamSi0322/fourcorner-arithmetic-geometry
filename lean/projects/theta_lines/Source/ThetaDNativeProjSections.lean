import ThetaDNativeProjRatios

namespace FourCorner.ThetaDNativeProjSections
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections ThetaDChartNaturality ThetaDNativeProjRatios
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 2500000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral (D ℚ) := original_integral
local instance (j : Fin 3) : Nonempty (B j) := basic_nonempty j

/-- The literal rational chart quotient mapped into the ACTUAL original
Proj structure sheaf, using native homogeneous localization sections. -/
def sections (j : Fin 3) : chartRing j →+* Γ(D ℚ,B j) :=
  (Proj.awayToSection G (hcoordinate j)).hom.comp
    (ThetaQuotientChart.chartInverse (targetEquation ℚ) (target_homogeneous ℚ) j)

 theorem sections_coordinate_generic (j : Fin 3) (a : Fin 2) :
    (D ℚ).germToFunctionField (B j) (sections j (Ideal.Quotient.mk _ (X a)))=
      ratio j (ThetaAmbientChart.insert 2 j a) := by
  apply stalkEquiv.injective
  rw [ratio,RingEquiv.apply_symm_apply]
  change Proj.stalkIso' G (genericPoint (D ℚ))
    ((D ℚ).presheaf.germ (B j) (genericPoint (D ℚ)) _ (sections j (Ideal.Quotient.mk _ (X a))))=_
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

/-- The native homogeneous-localization section map is also exactly the
contravariant structure-sheaf map of the literal chart isomorphism. -/
theorem sections_as_chart_app (j : Fin 3) :
    CommRingCat.ofHom (sections j)=
      (Scheme.ΓSpecIso (.of (chartRing j))).inv ≫
        (chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).hom.appTop ≫
        (B j).topIso.hom := by
  simp only [chartIso,ThetaQuotientChart.chartSchemeIso,Iso.trans_hom,Scheme.Hom.comp_appTop,
    Proj.basicOpenIsoSpec_hom,Proj.basicOpenToSpec_app_top]
  simp only [Scheme.Spec.mapIso_hom,Scheme.Spec_map]
  simp only [Category.assoc,Scheme.ΓSpecIso_naturality_assoc,Scheme.ΓSpecIso_naturality,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
  rfl

#print axioms sections_coordinate_generic
#print axioms sections_as_chart_app
end
end FourCorner.ThetaDNativeProjSections
