import ThetaGeometricContactPoints

namespace FourCorner.ThetaGeometricChartEvaluation
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections
open ThetaDFieldCoordinates ThetaDChartNaturality ThetaDCoordinateBasicOpens ThetaDSectionComparison
open SmoothProperRationalPointPlaces SchemePointStalkEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance (j : Fin 3) : IsOpenImmersion (chartMap j) := by unfold chartMap;infer_instance

 theorem germ_stalkMap_appLE {X Y : Scheme} (f : X ⟶ Y)
    (U : Y.Opens) (V : X.Opens) (e : V≤f ⁻¹ᵁ U) (x : X) (hx : x∈V) :
    Y.presheaf.germ U (f x) (e hx) ≫ f.stalkMap x=
      f.appLE U V e ≫ X.presheaf.germ V x hx := by
  rw [Scheme.Hom.appLE,Category.assoc,X.presheaf.germ_res]
  exact f.germ_stalkMap U x (e hx)

 theorem point_germ_appLE {X Y : Scheme} (f : X ⟶ Y)
    (q : Spec (.of K) ⟶ X) (U : Y.Opens) (e : (⊤ : X.Opens)≤f ⁻¹ᵁ U) :
    Y.presheaf.germ U ((q ≫ f) (IsLocalRing.closedPoint K)) (e trivial) ≫
      Scheme.stalkClosedPointTo (q ≫ f)=
        f.appLE U ⊤ e ≫ X.presheaf.germ ⊤ (q (IsLocalRing.closedPoint K)) trivial ≫
          Scheme.stalkClosedPointTo q := by
  rw [Scheme.stalkClosedPointTo_comp]
  exact (congrArg (fun g => g ≫ Scheme.stalkClosedPointTo q)
    (germ_stalkMap_appLE f U ⊤ e (q (IsLocalRing.closedPoint K)) trivial)).trans (Category.assoc _ _ _)

 theorem chart_section_evaluation (j : Fin 3) (vals : Fin 2 → K)
    (hv : ∀a : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation j a)=0)
    (r : chartRing j) :
    let ev := ThetaDGeometricChartPoints.evaluation j vals hv
    let p := Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ chartMap j
    Scheme.stalkClosedPointTo p
      ((D ℚ).presheaf.germ (U j) (p (IsLocalRing.closedPoint K))
        (by exact ⟨_,trivial,rfl⟩) ((sectionsRingEquiv j).symm r))=ev r := by
  dsimp only
  let ev := ThetaDGeometricChartPoints.evaluation j vals hv
  let q := Spec.map (CommRingCat.ofHom ev.toRingHom)
  have e : (⊤ : (Spec (.of (chartRing j))).Opens)≤chartMap j ⁻¹ᵁ U j := by
    intro x _;exact ⟨x,trivial,rfl⟩
  have h := point_germ_appLE (chartMap j) q (U j) e
  dsimp only [q] at h
  rw [Scheme.germ_stalkClosedPointTo_Spec] at h
  have hr : (chartMap j).appLE (U j) ⊤ e ((sectionsRingEquiv j).symm r)=
      (Scheme.ΓSpecIso (.of (chartRing j))).inv r := by
    apply (Scheme.ΓSpecIso (.of (chartRing j))).commRingCatIsoToRingEquiv.injective
    have hh := (sectionsRingEquiv j).apply_symm_apply r
    change (Scheme.ΓSpecIso (.of (chartRing j))).hom
      (((chartMap j).appIso ⊤).hom ((sectionsRingEquiv j).symm r))=r at hh
    rw [Scheme.Hom.appIso_hom'] at hh
    exact hh.trans ((Scheme.ΓSpecIso (.of (chartRing j))).commRingCatIsoToRingEquiv.apply_symm_apply r).symm
  have hh := congrArg (fun g : Γ(D ℚ,U j) ⟶ CommRingCat.of K => g.hom ((sectionsRingEquiv j).symm r)) h
  change _=ev ((Scheme.ΓSpecIso (.of (chartRing j))).hom ((chartMap j).appLE (U j) ⊤ e ((sectionsRingEquiv j).symm r))) at hh
  have hi : (Scheme.ΓSpecIso (.of (chartRing j))).hom
      ((Scheme.ΓSpecIso (.of (chartRing j))).inv r)=r :=
    (Scheme.ΓSpecIso (.of (chartRing j))).commRingCatIsoToRingEquiv.apply_symm_apply r
  rw [hr,hi] at hh
  exact hh

#print axioms germ_stalkMap_appLE
#print axioms point_germ_appLE
#print axioms chart_section_evaluation
end
end FourCorner.ThetaGeometricChartEvaluation
