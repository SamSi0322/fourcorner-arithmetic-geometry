import ThetaCoverClassPortable.ThetaActualPoints
import ThetaCoverClassPortable.ThetaSurvivingRealCoordinates
import ThetaCoverClassPortable.PolynomialPointTopology
import ThetaCoverClassPortable.MultiplicationComponentLocalCharts
import ThetaCoverClassPortable.ThetaHomogeneousEvaluation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Topology
namespace FourCorner.ThetaSurvivingNativeRealPath
open ThetaLiteralModels ThetaProjectiveModel
open ThetaLocalSurvival.StrongTopology ThetaLocalSurvival.Infinitesimal ThetaLocalSurvival.Multiplication

/-- The ORIGINAL literal C over QQ, with its original structural morphism. -/
abbrev sourceObject : Over base := Over.mk (cToBase ℚ)
abbrev sourceRing := affineRing (sourceEquation ℚ) 3
abbrev sourceZOpen := Proj.basicOpen (grading (sourceEquation ℚ) (source_homogeneous ℚ))
  (coordinate (sourceEquation ℚ) (source_homogeneous ℚ) 3)

/-- The original z=1 standard chart, as an actual over-QQ morphism. -/
def sourceChart : pointObject sourceRing ⟶ sourceObject :=
  Over.homMk ((chartIso (sourceEquation ℚ) (source_homogeneous ℚ) 3).inv≫sourceZOpen.ι)
    (ThetaModelBase.chart_over_base (sourceEquation ℚ) (source_homogeneous ℚ) 3)

/-- An actual point of the ORIGINAL rational affine coordinate ring from the given real tuple. -/
def chartEvaluation (v : ThetaSurvivingRealCoordinates.Chart) : sourceRing →ₐ[ℚ] ℝ :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval v.1) (by
    have h : ThetaQuotientChart.affineIdeal (sourceEquation ℚ) 3 ≤
        RingHom.ker (MvPolynomial.aeval v.1).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      fin_cases i
      all_goals simp [ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
        sourceEquation,ThetaActualPoints.source_drop,map_ofNat]
      · nlinarith [v.2.1]
      · nlinarith [v.2.2.1]
      · nlinarith [v.2.2.2]
    exact fun x hx => h hx)

@[simp] theorem chartEvaluation_X (v : ThetaSurvivingRealCoordinates.Chart) (i : Fin 4) :
    chartEvaluation v (Ideal.Quotient.mk _ (X i))=v.1 i := MvPolynomial.aeval_X _ _

/-- Continuity is derived by evaluation of each actual regular function on the quotient. -/
theorem chartEvaluation_continuous : Continuous chartEvaluation := by
  apply (continuous_affine_iff ℚ sourceRing ℝ _).2
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change Continuous (fun v : ThetaSurvivingRealCoordinates.Chart => MvPolynomial.aeval v.1 p)
  have h := (continuous_eval₂_point ℚ ℚ ℝ p).comp
    (continuous_const.prodMk continuous_subtype_val : Continuous
      (fun v : ThetaSurvivingRealCoordinates.Chart => ((Algebra.ofId ℚ ℝ : ℚ →ₐ[ℚ] ℝ),v.1)))
  exact h

/-- Genuine real points of the original C/QQ in the canonical strong topology. -/
def actualPoint (v : ThetaSurvivingRealCoordinates.Chart) : KPoints ℝ sourceObject :=
  pointChange (chartEvaluation v)≫sourceChart

theorem actualPoint_continuous : Continuous actualPoint :=
  (continuous_affineTest ℝ (CommAlgCat.of ℚ sourceRing) sourceChart).comp chartEvaluation_continuous

theorem actualPoint_left (v : ThetaSurvivingRealCoordinates.Chart) :
    (actualPoint v).left = Spec.map (CommRingCat.ofHom (chartEvaluation v).toRingHom)≫
      (chartIso (sourceEquation ℚ) (source_homogeneous ℚ) 3).inv≫sourceZOpen.ι := rfl

/-- The ORIGINAL OC=[1:1:1:1:0], as its actual original QQ-valued section. -/
def originalOrigin : rationalBase ⟶ sourceObject :=
  Over.homMk (ThetaActualPoints.originC (k:=ℚ))
    (ThetaActualPoints.boundaryPoint_over (k:=ℚ) (fun _ => true))

theorem chartEvaluation_origin : chartEvaluation (ThetaSurvivingRealCoordinates.chartPoint 0) =
    (Algebra.ofId ℚ ℝ).comp (ThetaActualPoints.boundaryEvaluation (k:=ℚ) (fun _ => true)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply]
  change chartEvaluation (ThetaSurvivingRealCoordinates.chartPoint 0) (Ideal.Quotient.mk _ (X i)) =
    (Algebra.ofId ℚ ℝ) (ThetaActualPoints.boundaryEvaluation (k:=ℚ) (fun _=>true) (Ideal.Quotient.mk _ (X i)))
  rw [chartEvaluation_X,ThetaActualPoints.boundaryEvaluation_X]
  rw [ThetaSurvivingRealCoordinates.origin_coordinates]
  fin_cases i <;> norm_num [ThetaActualPoints.sourceValues,ThetaActualPoints.sign]

/-- The path starts at the scalar extension of the ORIGINAL rational OC. -/
theorem actualPoint_origin : actualPoint (ThetaSurvivingRealCoordinates.chartPoint 0)=rationalScalarPoint ℝ originalOrigin := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (chartEvaluation (ThetaSurvivingRealCoordinates.chartPoint 0)).toRingHom)≫
      (chartIso (sourceEquation ℚ) (source_homogeneous ℚ) 3).inv≫sourceZOpen.ι =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ ℝ))≫ThetaActualPoints.originC (k:=ℚ)
  rw [chartEvaluation_origin]
  unfold ThetaActualPoints.originC ThetaActualPoints.boundaryPoint
  rw [←Spec.map_comp_assoc]
  rfl

def endpoint : KPoints ℝ sourceObject := actualPoint (ThetaSurvivingRealCoordinates.chartPoint 6)

/-- Actual continuous path in C(QQ)(R), with the canonical strong topology and original OC. -/
def originalRealPath : Path (rationalScalarPoint ℝ originalOrigin) endpoint where
  toFun u := actualPoint (ThetaSurvivingRealCoordinates.positivePath u)
  continuous_toFun := actualPoint_continuous.comp ThetaSurvivingRealCoordinates.positivePath.continuous
  source' := by rw [ThetaSurvivingRealCoordinates.positivePath.source,actualPoint_origin]
  target' := by rw [ThetaSurvivingRealCoordinates.positivePath.target]; rfl

end FourCorner.ThetaSurvivingNativeRealPath

