import ThetaDNativeProjSections

namespace FourCorner.ThetaDSectionComparison
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections
open ThetaDChartNaturality ThetaDNativeProjRatios ThetaDNativeProjSections
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral (D ℚ) := original_integral
local instance (j : Fin 3) : Nonempty (B j) := basic_nonempty j
local instance (j : Fin 3) : Nonempty (U j) := U_nonempty j
local instance (j : Fin 3) : IsOpenImmersion (chartMap j) := by unfold chartMap;infer_instance

 theorem sections_comparison_hom (j : Fin 3) :
    CommRingCat.ofHom (sections j) ≫
      (D ℚ).presheaf.map (eqToHom (U_eq_basic j)).op ≫
      ((chartMap j).appIso ⊤).hom ≫ (Scheme.ΓSpecIso (.of (chartRing j))).hom = 𝟙 _ := by
  have hB : (⊤ : (B j).toScheme.Opens) ≤ (B j).ι ⁻¹ᵁ B j := by
    intro p _;exact p.property
  have hfapp (h : ⊤ ≤ chartMap j ⁻¹ᵁ B j) :
      (chartMap j).appLE (B j) ⊤ h=
        (B j).topIso.inv ≫ (chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv.appTop := by
    change (((chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv) ≫ (B j).ι).appLE (B j) ⊤ _=_
    rw [←Scheme.Hom.appLE_comp_appLE _ _ (B j) ⊤ ⊤ hB (by simp)]
    change (B j).ι.appLE (B j) ⊤ hB ≫
      (chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv.appTop=_
    congr 1
  rw [sections_as_chart_app,Scheme.Hom.appIso_hom']
  dsimp only [U]
  simp only [Category.assoc,Scheme.Hom.map_appLE_assoc]
  rw [hfapp]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  rw [←Scheme.Hom.comp_appTop_assoc]
  simp

 theorem original_section_comparison (j : Fin 3) (r : chartRing j) :
    (D ℚ).germToFunctionField (U j) ((sectionsRingEquiv j).symm r)=
      (D ℚ).germToFunctionField (B j) (sections j r) := by
  have he : (sectionsRingEquiv j).symm r=
      ((D ℚ).presheaf.map (eqToHom (U_eq_basic j)).op).hom (sections j r) := by
    apply (sectionsRingEquiv j).injective
    rw [RingEquiv.apply_symm_apply]
    exact (congrArg (fun f : CommRingCat.of (chartRing j) ⟶ CommRingCat.of (chartRing j) => f.hom r)
      (sections_comparison_hom j)).symm
  rw [he]
  exact congrArg (fun f : Γ(D ℚ,B j) ⟶ (D ℚ).functionField => f.hom (sections j r))
    ((D ℚ).presheaf.germ_res (eqToHom (U_eq_basic j)) _ _)

#print axioms sections_comparison_hom
#print axioms original_section_comparison
end
end FourCorner.ThetaDSectionComparison
