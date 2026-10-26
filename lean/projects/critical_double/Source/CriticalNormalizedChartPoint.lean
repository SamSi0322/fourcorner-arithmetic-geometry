import CriticalChartResidueEvaluation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicCurve MvPolynomial
universe u
namespace FourCorner.CriticalNormalizedChartPoint
open CriticalProj23 CriticalStandardCharts CriticalChartBase CriticalHomogeneousEvaluation CriticalRadicalField
open CriticalSchemePointPlaces CriticalProjectiveResidues ResiduePlaceEvaluation CriticalChartResidueEvaluation
variable {k:Type u} [Field k]

lemma dehom_evaluate (j:Fin 4) (v:Fin 4→k) (hv:v j=1) :
 ((aeval (fun a:Fin 3=>v (CriticalAmbientChart.insert j a))).toRingHom).comp
  (CriticalAmbientChart.dehom k j)=MvPolynomial.eval v := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [CriticalAmbientChart.dehom]
  · intro a
    simp only [RingHom.comp_apply,CriticalAmbientChart.dehom,coe_eval₂Hom,eval₂_X]
    split_ifs with ha
    · simp [ha,hv]
    · simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,aeval_X,eval_X,CriticalAmbientChart.insert_drop j a ha]

lemma equations_evaluate (i:k) (v:Fin 4→k) (hc:CriticalElliptic23.CriticalCoordinates i v)
 (j:Fin 4) (hv:v j=1) (a:Fin 2) :
 aeval (fun b:Fin 3=>v (CriticalAmbientChart.insert j b)) (affineEquation i j a)=0 := by
  have he:=RingHom.congr_fun (dehom_evaluate j v hv) (equation i a)
  change aeval (fun b:Fin 3=>v (CriticalAmbientChart.insert j b)) (affineEquation i j a)=MvPolynomial.eval v (equation i a) at he
  rw [he]
  fin_cases a
  · simp only [equation,F0,MvPolynomial.eval_sub,MvPolynomial.eval_mul,MvPolynomial.eval_pow,MvPolynomial.eval_X,MvPolynomial.eval_C]
    exact sub_eq_zero.mpr hc.1
  · simp only [equation,F1,MvPolynomial.eval_sub,MvPolynomial.eval_mul,MvPolynomial.eval_pow,MvPolynomial.eval_X,MvPolynomial.eval_C]
    exact sub_eq_zero.mpr hc.2

def chartEvaluation (i:k) (j:Fin 4) (v:Fin 4→k)
 (hc:CriticalElliptic23.CriticalCoordinates i v) (hv:v j=1):affineRing i j→ₐ[k]k :=
 Ideal.Quotient.liftₐ (affineIdeal i j) (aeval (fun b:Fin 3=>v (CriticalAmbientChart.insert j b)))
  (by
    have hk:affineIdeal i j≤RingHom.ker (aeval (fun b:Fin 3=>v (CriticalAmbientChart.insert j b))).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact equations_evaluate i v hc j hv a
    exact fun x hx=>hk hx)

lemma chartEvaluation_ax (i:k) (j:Fin 4) (v:Fin 4→k)
 (hc:CriticalElliptic23.CriticalCoordinates i v) (hv:v j=1) (a:Fin 3):
 chartEvaluation i j v hc hv (CriticalChartJacobian.ax i j a)=v (CriticalAmbientChart.insert j a) := by
  change aeval (fun b:Fin 3=>v (CriticalAmbientChart.insert j b)) (X a)=_
  simp

lemma chartEvaluation_unique (i:k) (j:Fin 4) (f:affineRing i j→ₐ[k]k)
 (v:Fin 4→k) (hc:CriticalElliptic23.CriticalCoordinates i v) (hv:v j=1)
 (h:CriticalChartSmooth.normalizedVector j (fun a=>f (CriticalChartJacobian.ax i j a))=v) :
 f=chartEvaluation i j v hc hv := by
  apply CriticalBoundaryClassification.chart_hom_ext
  intro a
  rw [chartEvaluation_ax]
  have hh:=congrFun h (CriticalAmbientChart.insert j a)
  rwa [CriticalChartSmooth.normalizedVector_insert] at hh

/-- A genuine ORIGINAL Scheme point constructed directly from its literal
normalized Vj-chart values and the exact two original equations. -/
def point (i:k) (j:Fin 4) (v:Fin 4→k)
 (hc:CriticalElliptic23.CriticalCoordinates i v) (hv:v j=1):BasePoints i :=
 affinePoint i j (chartEvaluation i j v hc hv)

/-- This native constructor has EXACTLY the supplied original homogeneous
coordinates: every positive-degree homogeneous polynomial has its literal
principal-open pullback. This binds the tuple to the actual Scheme point. -/
theorem point_preimage_homogeneous (i:k) (j:Fin 4) (v:Fin 4→k)
 (hc:CriticalElliptic23.CriticalCoordinates i v) (hv:v j=1)
 (p:Ambient k) {d:ℕ} (hp:p.IsHomogeneous d) (hd:0<d) :
 (point i j v hc hv).val ⁻¹ᵁ Proj.basicOpen (criticalGrading i) ((qmap i) p)=
 PrimeSpectrum.basicOpen (MvPolynomial.eval v p) := by
  have h:=CriticalHomogeneousEvaluation.point_preimage i j (chartEvaluation i j v hc hv) p hp hd
  have he:chartEvaluation i j v hc hv (affineEvaluation i j p)=MvPolynomial.eval v p := by
    exact RingHom.congr_fun (dehom_evaluate j v hv) p
  exact h.trans (congrArg PrimeSpectrum.basicOpen he)

#print axioms chartEvaluation_unique
#print axioms point_preimage_homogeneous
end FourCorner.CriticalNormalizedChartPoint
