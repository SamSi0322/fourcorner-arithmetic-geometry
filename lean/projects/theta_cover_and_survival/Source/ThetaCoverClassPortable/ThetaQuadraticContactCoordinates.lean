import ThetaCoverClassPortable.ThetaQuadraticNativeDivisorIdentities

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
namespace FourCorner.ThetaQuadraticContactCoordinates
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticContactAlgebra ThetaQuadraticContactScheme
open ThetaQuadraticContactPlaces SmoothProperClosedPointPlaces
local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := fieldAlgebra
local instance : Nonempty (chartOpen 2) := chartOpen_nonempty 2
local instance : IsOpenImmersion (ThetaDPlaneChartSections.chartMap 2) := by
  unfold ThetaDPlaneChartSections.chartMap
  infer_instance

theorem point_germ_appLE_at {X Y : Scheme} (f : X ⟶ Y)
    (q : Spec (.of contactField) ⟶ X) (U : Y.Opens) (V : X.Opens) (e : V≤f ⁻¹ᵁ U)
    (hx : q (IsLocalRing.closedPoint contactField)∈V) :
    Y.presheaf.germ U ((q ≫ f) (IsLocalRing.closedPoint contactField)) (e hx) ≫
      Scheme.stalkClosedPointTo (q ≫ f)=
        f.appLE U V e ≫ X.presheaf.germ V (q (IsLocalRing.closedPoint contactField)) hx ≫
          Scheme.stalkClosedPointTo q := by
  rw [Scheme.stalkClosedPointTo_comp]
  exact (congrArg (fun g=>g ≫ Scheme.stalkClosedPointTo q)
    (ThetaGeometricChartEvaluation.germ_stalkMap_appLE f U V e _ hx)).trans (Category.assoc _ _ _)

theorem contact_in_chart (b : Bool) : (closedContact b).val∈chartOpen 2 := by
  change (contactMap b ≫ toRational) (IsLocalRing.closedPoint contactField)∈ThetaDPlaneChartSections.U 2
  rw [contactMap_toRational]
  exact ⟨_,trivial,rfl⟩

def coordinateSection (a : Fin 2) : Γ(curve,chartOpen 2) :=
  (toRational.app (ThetaDPlaneChartSections.U 2)).hom
    ((ThetaDPlaneChartSections.sectionsRingEquiv 2).symm (Ideal.Quotient.mk _ (X a)))

def coordinateValue (b : Bool) (a : Fin 2) : (contactPlace b).toValuationSubring :=
  stalkValuationEquiv toBase (closedContact b)
    (curve.presheaf.germ (chartOpen 2) (closedContact b).val (contact_in_chart b) (coordinateSection a))

theorem coordinateValue_coe (b : Bool) (a : Fin 2) :
    (coordinateValue b a : functionField)=coordinate 2 a := by
  rw [coordinateValue,stalkValuationEquiv_coe]
  exact curve.algebraMap_germ_eq_germToFunctionField (contact_in_chart b) (coordinateSection a)

theorem original_section_evaluation (b : Bool) (r : ThetaDPlaneChartSections.chartRing 2) :
    Scheme.stalkClosedPointTo (rationalChartPoint b)
      ((ThetaLiteralModels.D ℚ).presheaf.germ (ThetaDPlaneChartSections.U 2)
        (rationalChartPoint b (IsLocalRing.closedPoint contactField))
        (by exact ⟨_,trivial,rfl⟩) ((ThetaDPlaneChartSections.sectionsRingEquiv 2).symm r))=
      chartEvaluation b r := by
  let q := Spec.map (CommRingCat.ofHom (chartEvaluation b).toRingHom)
  have e : (⊤ : (Spec (.of (ThetaDPlaneChartSections.chartRing 2))).Opens)≤
      ThetaDPlaneChartSections.chartMap 2 ⁻¹ᵁ ThetaDPlaneChartSections.U 2 := by
    intro x _;exact ⟨x,trivial,rfl⟩
  have h := point_germ_appLE_at (ThetaDPlaneChartSections.chartMap 2) q
    (ThetaDPlaneChartSections.U 2) ⊤ e (by trivial)
  dsimp only [q] at h
  rw [Scheme.germ_stalkClosedPointTo_Spec] at h
  have hr : (ThetaDPlaneChartSections.chartMap 2).appLE (ThetaDPlaneChartSections.U 2) ⊤ e
      ((ThetaDPlaneChartSections.sectionsRingEquiv 2).symm r)=
      (Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).inv r := by
    apply (Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).commRingCatIsoToRingEquiv.injective
    have hh := (ThetaDPlaneChartSections.sectionsRingEquiv 2).apply_symm_apply r
    change (Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).hom
      (((ThetaDPlaneChartSections.chartMap 2).appIso ⊤).hom
        ((ThetaDPlaneChartSections.sectionsRingEquiv 2).symm r))=r at hh
    rw [Scheme.Hom.appIso_hom'] at hh
    exact hh.trans ((Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).commRingCatIsoToRingEquiv.apply_symm_apply r).symm
  have hh := congrArg (fun g : Γ(ThetaLiteralModels.D ℚ,ThetaDPlaneChartSections.U 2) ⟶ CommRingCat.of contactField =>
    g.hom ((ThetaDPlaneChartSections.sectionsRingEquiv 2).symm r)) h
  change _=chartEvaluation b ((Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).hom
    ((ThetaDPlaneChartSections.chartMap 2).appLE (ThetaDPlaneChartSections.U 2) ⊤ e
      ((ThetaDPlaneChartSections.sectionsRingEquiv 2).symm r))) at hh
  rw [hr] at hh
  have hi : (Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).hom
      ((Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).inv r)=r :=
    (Scheme.ΓSpecIso (.of (ThetaDPlaneChartSections.chartRing 2))).commRingCatIsoToRingEquiv.apply_symm_apply r
  rw [hi] at hh
  exact hh

theorem coordinate_stalk_evaluation (b : Bool) (a : Fin 2) :
    Scheme.stalkClosedPointTo (contactMap b)
      (curve.presheaf.germ (chartOpen 2) (closedContact b).val (contact_in_chart b)
        (coordinateSection a))=values b a := by
  let s := (ThetaDPlaneChartSections.sectionsRingEquiv 2).symm (Ideal.Quotient.mk _ (X a))
  have hc := point_germ_appLE_at toRational (contactMap b) (ThetaDPlaneChartSections.U 2)
    (chartOpen 2) le_rfl (contact_in_chart b)
  have hh := congrArg (fun g : Γ(ThetaLiteralModels.D ℚ,ThetaDPlaneChartSections.U 2) ⟶ CommRingCat.of contactField => g.hom s) hc
  change Scheme.stalkClosedPointTo (contactMap b ≫ toRational)
      ((ThetaLiteralModels.D ℚ).presheaf.germ (ThetaDPlaneChartSections.U 2)
        ((contactMap b ≫ toRational) (IsLocalRing.closedPoint contactField)) _ s)=
    Scheme.stalkClosedPointTo (contactMap b)
      (curve.presheaf.germ (chartOpen 2) (closedContact b).val _
        ((toRational.appLE (ThetaDPlaneChartSections.U 2) (chartOpen 2) le_rfl).hom s)) at hh
  rw [Scheme.Hom.appLE_eq_app] at hh
  have hOrig (p : Spec (.of contactField) ⟶ ThetaLiteralModels.D ℚ)
      (hp : p (IsLocalRing.closedPoint contactField)∈ThetaDPlaneChartSections.U 2)
      (he : p=rationalChartPoint b) :
      Scheme.stalkClosedPointTo p ((ThetaLiteralModels.D ℚ).presheaf.germ
        (ThetaDPlaneChartSections.U 2) (p (IsLocalRing.closedPoint contactField)) hp s)=values b a := by
    subst p
    exact (original_section_evaluation b _).trans (chartEvaluation_X b a)
  exact hh.symm.trans (hOrig _ _ (contactMap_toRational b))

theorem coordinateValue_eval (b : Bool) (a : Fin 2) :
    valuationEvaluation b (coordinateValue b a)=values b a := by
  letI := SchemePointStalkEvaluation.stalkAlgebra toBase (closedContact b).val
  change (Scheme.stalkClosedPointTo (contactMap b)).hom
    ((stalkValuationEquiv toBase (closedContact b)).symm
      ((stalkValuationEquiv toBase (closedContact b))
        (curve.presheaf.germ (chartOpen 2) (closedContact b).val (contact_in_chart b)
          (coordinateSection a))))=values b a
  rw [RingEquiv.symm_apply_apply]
  exact coordinate_stalk_evaluation b a

end FourCorner.ThetaQuadraticContactCoordinates
