import ThetaCoverClassPortable.ThetaCoverBoundaryPoints
import ThetaCoverClassPortable.ThetaGaloisFieldAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
namespace FourCorner.ThetaCoverRationalData
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaCoverFunctions ThetaCoverBoundaryPoints
open ThetaLiteralModels ThetaDPlaneChartSections ThetaDChartNaturality ThetaDNativeProjRatios
open ThetaNativeFunctionFieldMap ThetaDExactChartTransitions
local instance : IsIntegral (D ℚ) := original_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : Surjective qb := qb_surjective
local instance : Surjective (pullback.fst (dToBase ℚ) qb) := inferInstance

abbrev rationalField := (D ℚ).functionField
/-- Literal h in the generic stalk of the ORIGINAL rational projective D. -/
def rationalH : rationalField := (ratio 2 0^2+ratio 2 1^2-2)/2

 theorem rationalH_image : fieldMap (pullback.fst (dToBase ℚ) qb) rationalH=h := by
  have hx : fieldMap (pullback.fst (dToBase ℚ) qb) (ratio 2 0)=x :=
    (coordinate_eq_native_ratio 2 0).symm
  have hy : fieldMap (pullback.fst (dToBase ℚ) qb) (ratio 2 1)=y :=
    (coordinate_eq_native_ratio 2 1).symm
  unfold rationalH h c0
  rw [map_div₀,map_sub,map_add,map_pow,map_pow,map_ofNat,hx,hy]

 theorem rationalH_ne_zero : rationalH≠0 := by
  intro hh
  have he:=rationalH_image
  rw [hh,map_zero] at he
  exact h_ne_zero he.symm

abbrev rationalValues (e : Signs) : Fin 2→ℚ := ![sign e.1,sign e.2]
 theorem rational_relations (e : Signs) (a : Fin 1) :
    MvPolynomial.aeval (rationalValues e) (ThetaDGeometricChartPoints.equation 2 a)=0 := by
  rcases e with ⟨b,c⟩
  cases b <;> cases c <;> fin_cases a <;>
    norm_num [rationalValues,ThetaActualPoints.sign,ThetaDGeometricChartPoints.equation,
      ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,ThetaLiteralModels.targetEquation,
      ThetaLiteralModels.targetPolynomial,ThetaTargetSmooth.drop_table,Fin.isValue] <;> simp <;> norm_num

/-- An actual rational chart-algebra map, not just a Galois-fixed label. -/
def rationalEvaluation (e : Signs) : chartRing 2 →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (rationalValues e)) (by
    have hh : ThetaQuotientChart.affineIdeal (targetEquation ℚ) 2 ≤
        RingHom.ker (MvPolynomial.aeval (rationalValues e)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact rational_relations e a
    exact fun x hx=>hh hx)

@[simp] theorem rationalEvaluation_X (e : Signs) (a : Fin 2) :
    rationalEvaluation e (Ideal.Quotient.mk _ (X a))=rationalValues e a :=
  MvPolynomial.aeval_X _ _

/-- Genuine rational point of the SAME rational Proj scheme D. -/
def rationalPoint (e : Signs) : Spec (.of ℚ) ⟶ D ℚ :=
  Spec.map (CommRingCat.ofHom (rationalEvaluation e).toRingHom) ≫ chartMap 2

 theorem rationalPoint_over (e : Signs) : rationalPoint e ≫ dToBase ℚ=𝟙 _ :=
  ThetaSourceComparison.rational_base_unique _ _

 theorem rational_values_map (e : Signs) (a : Fin 2) :
    algebraMap ℚ K (rationalValues e a)=values e a := by
  rcases e with ⟨b,c⟩
  cases b <;> cases c <;> fin_cases a <;> norm_num [rationalValues,values,ThetaActualPoints.sign]

 theorem evaluation_descends (e : Signs) :
    (ThetaDGeometricChartPoints.evaluation 2 (values e) (relations e)).toRingHom=
      (algebraMap ℚ K).comp (rationalEvaluation e).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro q
    simp only [RingHom.comp_apply,Ideal.Quotient.lift_mk,Ideal.Quotient.liftₐ_apply,
      ThetaDGeometricChartPoints.evaluation,rationalEvaluation,MvPolynomial.aeval_C]
    simp
  · intro a
    simp only [RingHom.comp_apply]
    change ThetaDGeometricChartPoints.evaluation 2 (values e) (relations e) (Ideal.Quotient.mk _ (X a))=
      algebraMap ℚ K (rationalEvaluation e (Ideal.Quotient.mk _ (X a)))
    rw [ThetaDGeometricChartPoints.evaluation_X,rationalEvaluation_X]
    exact (rational_values_map e a).symm

/-- Actual descent diagram for each of the four points. The geometric point
used to define E0 is exactly the pullback of the displayed rational point. -/
theorem rationalPoint_basechange (e : Signs) :
    (point e).val ≫ pullback.fst (dToBase ℚ) qb=qb ≫ rationalPoint e := by
  change ThetaDGeometricChartPoints.point 2 (values e) (relations e) ≫ pullback.fst (dToBase ℚ) qb=_
  simp only [ThetaDGeometricChartPoints.point,pullback.lift_fst]
  change Spec.map (CommRingCat.ofHom
      (ThetaDGeometricChartPoints.evaluation 2 (values e) (relations e)).toRingHom) ≫ chartMap 2=_
  rw [evaluation_descends]
  change Spec.map (CommRingCat.ofHom ((algebraMap ℚ K).comp (rationalEvaluation e).toRingHom)) ≫ chartMap 2=_
  rw [CommRingCat.ofHom_comp,Spec.map_comp]
  rfl

 theorem rational_origin_preserved : rationalPoint (true,true)=ThetaActualPoints.originD (k:=ℚ) := by
  have he : rationalEvaluation (true,true)=ThetaActualPoints.originDEvaluation (k:=ℚ) := by
    apply AlgHom.ext
    intro q
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
    change MvPolynomial.aeval (rationalValues (true,true)) p=MvPolynomial.aeval (fun _=>1) p
    have hv : rationalValues (true,true)=(fun _ : Fin 2=> (1:ℚ)) := by
      funext a
      fin_cases a <;> rfl
    rw [hv]
  unfold rationalPoint ThetaActualPoints.originD
  rw [he]
  rfl

#print axioms rationalH_image
#print axioms rationalPoint_basechange
end FourCorner.ThetaCoverRationalData
