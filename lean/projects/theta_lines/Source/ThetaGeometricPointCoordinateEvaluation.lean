import ThetaGeometricChartEvaluation

namespace FourCorner.ThetaGeometricPointCoordinateEvaluation
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections
open ThetaDFieldCoordinates ThetaDChartNaturality ThetaDCoordinateBasicOpens
open ThetaGeometricChartEvaluation SmoothProperRationalPointPlaces SchemePointStalkEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

 theorem point_germ_appLE_at {X Y : Scheme} (f : X ⟶ Y)
    (q : Spec (.of K) ⟶ X) (U : Y.Opens) (V : X.Opens) (e : V≤f ⁻¹ᵁ U)
    (hx : q (IsLocalRing.closedPoint K)∈V) :
    Y.presheaf.germ U ((q ≫ f) (IsLocalRing.closedPoint K)) (e hx) ≫
      Scheme.stalkClosedPointTo (q ≫ f)=
        f.appLE U V e ≫ X.presheaf.germ V (q (IsLocalRing.closedPoint K)) hx ≫
          Scheme.stalkClosedPointTo q := by
  rw [Scheme.stalkClosedPointTo_comp]
  exact (congrArg (fun g=>g ≫ Scheme.stalkClosedPointTo q)
    (germ_stalkMap_appLE f U V e (q (IsLocalRing.closedPoint K)) hx)).trans (Category.assoc _ _ _)

 theorem geometric_point_in_chart (j : Fin 3) (vals : Fin 2 → K)
    (hv : ∀a : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation j a)=0) :
    ThetaDGeometricChartPoints.point j vals hv (IsLocalRing.closedPoint K)∈geoU j := by
  change pullback.fst (dToBase ℚ) qb
    (ThetaDGeometricChartPoints.point j vals hv (IsLocalRing.closedPoint K))∈U j
  change (ThetaDGeometricChartPoints.point j vals hv ≫ pullback.fst (dToBase ℚ) qb)
    (IsLocalRing.closedPoint K)∈U j
  simp only [ThetaDGeometricChartPoints.point,pullback.lift_fst]
  exact ⟨_,trivial,rfl⟩

/-- Actual stalk evaluation of EVERY actual geometric chart coordinate
matches its literal value, preserving the original rational chart and the
categorical Qbar pullback diagram throughout. -/
theorem coordinate_stalk_evaluation (j : Fin 3) (vals : Fin 2 → K)
    (hv : ∀a : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation j a)=0)
    (a : Fin 2) :
    Scheme.stalkClosedPointTo (ThetaDGeometricChartPoints.point j vals hv)
      (geometricD.presheaf.germ (geoU j)
        (ThetaDGeometricChartPoints.point j vals hv (IsLocalRing.closedPoint K))
        (geometric_point_in_chart j vals hv) (coordinateSection j a))=vals a := by
  let q := ThetaDGeometricChartPoints.point j vals hv
  let f := pullback.fst (dToBase ℚ) qb
  let s := (sectionsRingEquiv j).symm (Ideal.Quotient.mk _ (X a))
  have hq : q ≫ f=Spec.map (CommRingCat.ofHom (ThetaDGeometricChartPoints.evaluation j vals hv).toRingHom) ≫ chartMap j := by
    simp only [q,f,ThetaDGeometricChartPoints.point,pullback.lift_fst,
      ThetaDGeometricChartPoints.toOriginal,chartMap]
  have hsec : (f.appLE (U j) (geoU j) le_rfl).hom s=coordinateSection j a := by
    change (f.appLE (U j) (f ⁻¹ᵁ U j) le_rfl).hom s=_
    rw [Scheme.Hom.appLE_eq_app]
    exact (actualChartEquiv_one_tmul j (Ideal.Quotient.mk _ (X a))).symm
  have hOrig : (q ≫ f) (IsLocalRing.closedPoint K)∈U j := geometric_point_in_chart j vals hv
  have hc := point_germ_appLE_at f q (U j) (geoU j) le_rfl (geometric_point_in_chart j vals hv)
  have hh := congrArg (fun g : Γ(D ℚ,U j) ⟶ CommRingCat.of K => g.hom s) hc
  change Scheme.stalkClosedPointTo (q ≫ f)
    ((D ℚ).presheaf.germ (U j) ((q ≫ f) (IsLocalRing.closedPoint K)) _ s)=
      Scheme.stalkClosedPointTo q (geometricD.presheaf.germ (geoU j) (q (IsLocalRing.closedPoint K)) _
        ((f.appLE (U j) (geoU j) le_rfl).hom s)) at hh
  rw [hsec] at hh
  have hvalue (p : Spec (.of K) ⟶ D ℚ)
      (hp : p (IsLocalRing.closedPoint K)∈U j)
      (he : p=Spec.map (CommRingCat.ofHom (ThetaDGeometricChartPoints.evaluation j vals hv).toRingHom) ≫ chartMap j) :
      Scheme.stalkClosedPointTo p ((D ℚ).presheaf.germ (U j) (p (IsLocalRing.closedPoint K)) hp s)=vals a := by
    subst p
    simpa only [s,ThetaDGeometricChartPoints.evaluation_X] using
      (chart_section_evaluation j vals hv (Ideal.Quotient.mk _ (X a)))
  have ho := hvalue (q ≫ f) hOrig hq
  exact hh.symm.trans ho

#print axioms point_germ_appLE_at
#print axioms geometric_point_in_chart
#print axioms coordinate_stalk_evaluation
end
end FourCorner.ThetaGeometricPointCoordinateEvaluation
