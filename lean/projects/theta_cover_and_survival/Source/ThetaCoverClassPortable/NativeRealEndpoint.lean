import ThetaCoverClassPortable.NativeRealPath

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

abbrev sourceTOpen := Proj.basicOpen (grading (sourceEquation ℚ) (source_homogeneous ℚ))
  (coordinate (sourceEquation ℚ) (source_homogeneous ℚ) 4)

/-- Original standard chart for any projective coordinate, as an over-QQ morphism. -/
def standardChart (j : Fin 5) : pointObject (affineRing (sourceEquation ℚ) j) ⟶ sourceObject :=
  Over.homMk ((chartIso (sourceEquation ℚ) (source_homogeneous ℚ) j).inv≫
    (Proj.basicOpen (grading (sourceEquation ℚ) (source_homogeneous ℚ))
      (coordinate (sourceEquation ℚ) (source_homogeneous ℚ) j)).ι)
    (ThetaModelBase.chart_over_base (sourceEquation ℚ) (source_homogeneous ℚ) j)

def standardPoint (j : Fin 5) (f : affineRing (sourceEquation ℚ) j →ₐ[ℚ] ℝ) : KPoints ℝ sourceObject :=
  pointChange f≫standardChart j

/-- Homogeneous coordinates actually evaluated through the original rational chart ring. -/
def homogeneousCoordinates (j : Fin 5) (f : affineRing (sourceEquation ℚ) j →ₐ[ℚ] ℝ) (i : Fin 5) : ℝ :=
  f (ThetaHomogeneousEvaluation.affineEvaluation (sourceEquation ℚ) j (X i))

theorem homogeneousCoordinates_zChart (v : ThetaSurvivingRealCoordinates.Chart) :
    homogeneousCoordinates 3 (chartEvaluation v)=![v.1 0,v.1 1,v.1 2,1,v.1 3] := by
  funext i
  fin_cases i <;> simp [homogeneousCoordinates,ThetaHomogeneousEvaluation.affineEvaluation,
    ThetaAmbientChart.dehom,ThetaActualPoints.source_drop,chartEvaluation_X]

/-- Literal T=1 metric inequalities of eq:theta-U, expressed through homogeneous ratios. -/
def strictHomogeneous (w : Fin 5 → ℝ) : Prop :=
  w 4≠0 ∧ 1<w 0/w 4 ∧ 0<w 1/w 4 ∧ 0<w 2/w 4 ∧
    w 0/w 4+7*|w 3/w 4|<50

/-- The paper's U on the ORIGINAL C/QQ real-point space. The union ranges over ALL
original affine charts; it imposes exactly the displayed T-normalized inequalities. -/
def paperU : Set (KPoints ℝ sourceObject) :=
  {P | ∃ (j : Fin 5) (f : affineRing (sourceEquation ℚ) j →ₐ[ℚ] ℝ),
    standardPoint j f=P ∧ strictHomogeneous (homogeneousCoordinates j f)}

/-- T's actual homogeneous basic open pulls back to the nonzero evaluated coordinate. -/
theorem actualPoint_T_preimage (v : ThetaSurvivingRealCoordinates.Chart) :
    (actualPoint v).left ⁻¹ᵁ sourceTOpen=PrimeSpectrum.basicOpen (v.1 3) := by
  rw [actualPoint_left]
  have h := ThetaHomogeneousEvaluation.point_preimage (sourceEquation ℚ) (source_homogeneous ℚ)
    3 (chartEvaluation v) (X 4) (isHomogeneous_X _ _) (by decide : 0<1)
  have he : chartEvaluation v (ThetaHomogeneousEvaluation.affineEvaluation (sourceEquation ℚ) 3 (X 4))=v.1 3 := by
    have he := congrFun (homogeneousCoordinates_zChart v) 4
    change chartEvaluation v (ThetaHomogeneousEvaluation.affineEvaluation (sourceEquation ℚ) 3 (X 4))=v.1 3 at he
    exact he
  exact h.trans (congrArg PrimeSpectrum.basicOpen he)

theorem actualPoint_T_nonzero_iff (v : ThetaSurvivingRealCoordinates.Chart) :
    pointSupport ℝ (actualPoint v)∈sourceTOpen ↔ v.1 3≠0 := by
  change (IsLocalRing.closedPoint ℝ)∈(actualPoint v).left ⁻¹ᵁ sourceTOpen ↔ _
  rw [actualPoint_T_preimage]
  change v.1 3∉(IsLocalRing.closedPoint ℝ).asIdeal ↔ v.1 3≠0
  simp [IsLocalRing.closedPoint,IsLocalRing.maximalIdeal_eq_bot]

theorem originalRealPath_nonboundary (u : unitInterval) (hu : 0<(u:ℝ)) :
    pointSupport ℝ (originalRealPath u)∈sourceTOpen := by
  apply (actualPoint_T_nonzero_iff _).mpr
  exact ne_of_gt (ThetaSurvivingRealCoordinates.path_nonboundary u hu)

theorem endpoint_strictHomogeneous :
    strictHomogeneous (homogeneousCoordinates 3 (chartEvaluation (ThetaSurvivingRealCoordinates.chartPoint 6))) := by
  rw [homogeneousCoordinates_zChart]
  unfold strictHomogeneous
  simp only [ThetaSurvivingRealCoordinates.endpoint_coordinates,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  exact ⟨by norm_num,ThetaSurvivingRealCoordinates.endpoint_strict_metric⟩

theorem endpoint_mem_paperU : endpoint∈paperU :=
  ⟨3,chartEvaluation (ThetaSurvivingRealCoordinates.chartPoint 6),rfl,endpoint_strictHomogeneous⟩

theorem endpoint_T_nonzero : pointSupport ℝ endpoint∈sourceTOpen := by
  apply (actualPoint_T_nonzero_iff _).mpr
  change (6:ℝ)≠0
  norm_num

def metricX (w : Fin 5 → ℝ) : ℝ := (50-w 0/w 4-7*(w 3/w 4))/100
def metricY (w : Fin 5 → ℝ) : ℝ := (50-w 0/w 4+7*(w 3/w 4))/100
def endpointX : ℝ := metricX (homogeneousCoordinates 3 (chartEvaluation (ThetaSurvivingRealCoordinates.chartPoint 6)))
def endpointY : ℝ := metricY (homogeneousCoordinates 3 (chartEvaluation (ThetaSurvivingRealCoordinates.chartPoint 6)))

theorem endpoint_y_sub_x : endpointY-endpointX=7/300 := by
  unfold endpointY endpointX
  rw [homogeneousCoordinates_zChart]
  simp only [metricY,metricX,ThetaSurvivingRealCoordinates.endpoint_coordinates,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]
  exact ThetaSurvivingRealCoordinates.endpoint_off_diagonal

theorem endpoint_x_ne_y : endpointX≠endpointY := by
  intro h
  have hd := endpoint_y_sub_x
  rw [h,sub_self] at hd
  norm_num at hd

/-- Consumable actual C/QQ real path and strict off-diagonal endpoint package.
This makes no Jacobian or surviving-cover claim by itself. -/
theorem actual_C_real_path_package :
    Continuous actualPoint ∧ Nonempty (Path (rationalScalarPoint ℝ originalOrigin) endpoint) ∧
    endpoint∈paperU ∧ pointSupport ℝ endpoint∈sourceTOpen ∧
    endpointY-endpointX=7/300 ∧ endpointX≠endpointY :=
  ⟨actualPoint_continuous,⟨originalRealPath⟩,endpoint_mem_paperU,endpoint_T_nonzero,
    endpoint_y_sub_x,endpoint_x_ne_y⟩

end FourCorner.ThetaSurvivingNativeRealPath
