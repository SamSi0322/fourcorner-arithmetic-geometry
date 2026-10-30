import ThetaDCoordinateBasicOpens

namespace FourCorner.ThetaDOriginalChartOpens
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDPlaneChartSections ThetaDNativeProjRatios
open ThetaDNativeProjSections ThetaDSectionComparison ThetaDCoordinateBasicOpens
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance (j : Fin 3) : IsOpenImmersion (chartMap j) := by unfold chartMap;infer_instance

 theorem chart_into_basic (j : Fin 3) : (⊤ : (Spec (.of (chartRing j))).Opens)≤chartMap j ⁻¹ᵁ B j := by
  intro x _
  exact ((chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv x).property

 theorem chart_section_appLE (j : Fin 3) :
    CommRingCat.ofHom (sections j) ≫ (chartMap j).appLE (B j) ⊤ (chart_into_basic j)=
      (Scheme.ΓSpecIso (.of (chartRing j))).inv := by
  apply (cancel_mono (Scheme.ΓSpecIso (.of (chartRing j))).hom).mp
  rw [Category.assoc,Iso.inv_hom_id]
  have hh := sections_comparison_hom j
  rw [Scheme.Hom.appIso_hom'] at hh
  dsimp only [U] at hh
  simpa only [Category.assoc,Scheme.Hom.map_appLE_assoc] using hh

/-- Exact original Proj chart transitions at the level of ACTUAL opens,
including specialization at every scheme point, not only generic germs. -/
theorem chart_preimage_basic (j : Fin 3) (a : Fin 2) :
    chartMap j ⁻¹ᵁ B (ThetaAmbientChart.insert 2 j a)=
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk _ (X a)) := by
  have hb := Scheme.basicOpen_appLE (chartMap j) ⊤ (B j) (chart_into_basic j)
    (sections j (Ideal.Quotient.mk _ (X a)))
  have hr := congrArg (fun f : CommRingCat.of (chartRing j) ⟶
      Γ(Spec (.of (chartRing j)),⊤) => f.hom (Ideal.Quotient.mk _ (X a))) (chart_section_appLE j)
  change (chartMap j).appLE (B j) ⊤ (chart_into_basic j) (sections j (Ideal.Quotient.mk _ (X a)))=
    (Scheme.ΓSpecIso (.of (chartRing j))).inv (Ideal.Quotient.mk _ (X a)) at hr
  rw [hr,basicOpen_eq_of_affine,native_coordinate_basicOpen] at hb
  have ht : chartMap j ⁻¹ᵁ B j=⊤ := top_unique (chart_into_basic j)
  change _=⊤ ⊓ ((chartMap j ⁻¹ᵁ B j) ⊓ (chartMap j ⁻¹ᵁ B (ThetaAmbientChart.insert 2 j a))) at hb
  rw [ht] at hb
  simpa using hb.symm

#print axioms chart_section_appLE
#print axioms chart_preimage_basic
end
end FourCorner.ThetaDOriginalChartOpens
