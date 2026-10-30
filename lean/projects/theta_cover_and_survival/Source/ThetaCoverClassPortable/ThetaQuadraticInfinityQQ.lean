import ThetaCoverClassPortable.ActualQuadraticTensorBaseChange

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial

namespace FourCorner.ThetaQuadraticInfinityQQ
abbrev residueField := QuadraticAlgebra ℚ (-2) 0
instance irreducible : Fact (∀ q : ℚ,q^2 ≠ -2+0*q) :=
  ⟨fun q => by nlinarith [sq_nonneg q]⟩
def radical : residueField := QuadraticAlgebra.omega
theorem radical_sq : radical^2=(-2:residueField) := by
  unfold radical
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_neg,map_ofNat,map_zero,zero_mul,add_zero]

def sign (branch : Bool) : ℚ := if branch then 1 else -1
def parameter (branch : Bool) : residueField :=
  (algebraMap ℚ residueField (sign branch)+70*radical)/99

theorem quadratic_relation (branch : Bool) :
    99*(parameter branch)^2-2*algebraMap ℚ residueField (sign branch)*parameter branch+99=0 := by
  cases branch <;> simp only [parameter,sign,Bool.false_eq_true,if_false,if_true,map_neg,map_one]
  all_goals
    ring_nf
    rw [radical_sq]
    norm_num

theorem quartic_relation (branch : Bool) :
    9801*(parameter branch)^4+19598*(parameter branch)^2+9801=0 := by
  have hf (z : residueField) : 9801*z^4+19598*z^2+9801=
      (99*z^2-2*z+99)*(99*z^2+2*z+99) := by ring
  rw [hf]
  have h := quadratic_relation branch
  cases branch
  · have hh : 99*(parameter false)^2+2*parameter false+99=0 := by
      simpa only [sign,Bool.false_eq_true,if_false,map_neg,map_one,mul_neg,neg_mul,mul_one,sub_neg_eq_add] using h
    rw [hh,mul_zero]
  · have hh : 99*(parameter true)^2-2*parameter true+99=0 := by
      simpa only [sign,if_true,map_one,mul_one] using h
    rw [hh,zero_mul]

def values (branch : Bool) : Fin 2 → residueField := ![parameter branch,0]
theorem relations (branch : Bool) (a : Fin 1) :
    MvPolynomial.aeval (values branch) (ThetaDGeometricChartPoints.equation 0 a)=0 := by
  fin_cases a
  norm_num [ThetaDGeometricChartPoints.equation,ThetaQuotientChart.affineEquation,
    ThetaAmbientChart.dehom,ThetaLiteralModels.targetEquation,ThetaLiteralModels.targetPolynomial,
    ThetaTargetSmooth.drop_table,Fin.isValue,values]
  simp
  linear_combination quartic_relation branch

def evaluation (branch : Bool) : ThetaDPlaneChartSections.chartRing 0 →ₐ[ℚ] residueField :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (values branch)) (by
    have hh : ThetaQuotientChart.affineIdeal (ThetaLiteralModels.targetEquation ℚ) 0 ≤
        RingHom.ker (MvPolynomial.aeval (values branch)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact relations branch a
    exact fun z hz=>hh hz)

@[simp] theorem evaluation_X (branch : Bool) (a : Fin 2) :
    evaluation branch (Ideal.Quotient.mk _ (X a))=values branch a := MvPolynomial.aeval_X _ _

def chartRadical (branch : Bool) : ThetaDPlaneChartSections.chartRing 0 :=
  (99*(Ideal.Quotient.mk _ (X 0))-algebraMap ℚ _ (sign branch))*algebraMap ℚ _ (1/70)

theorem evaluation_surjective (branch : Bool) : Function.Surjective (evaluation branch) := by
  have hg : evaluation branch (Ideal.Quotient.mk _
      ((C 99*X 0-C (sign branch))*C (1/70)))=radical := by
    simp [evaluation,values]
    unfold parameter
    norm_num
    ring
  rintro ⟨a,b⟩
  refine ⟨algebraMap ℚ _ a + algebraMap ℚ _ b *
    (Ideal.Quotient.mk _ ((C 99*X 0-C (sign branch))*C (1/70))),?_⟩
  rw [map_add,map_mul,AlgHom.commutes,AlgHom.commutes,hg]
  apply QuadraticAlgebra.ext <;> simp [radical,QuadraticAlgebra.algebraMap_eq]

def point (branch : Bool) : Spec (.of residueField) ⟶ ThetaLiteralModels.D ℚ :=
  Spec.map (CommRingCat.ofHom (evaluation branch).toRingHom) ≫ ThetaDPlaneChartSections.chartMap 0
theorem point_over (branch : Bool) : point branch ≫ ThetaLiteralModels.dToBase ℚ=
    Scheme.TwoAffineOpenCover.specMap ℚ residueField :=
  ThetaSourceComparison.rational_base_unique _ _

theorem point_closedImmersion (branch : Bool) : IsClosedImmersion (point branch) := by
  letI := ThetaLiteralModels.d_proper ℚ
  letI : IsOpenImmersion (ThetaDPlaneChartSections.chartMap 0) := by
    unfold ThetaDPlaneChartSections.chartMap
    infer_instance
  letI := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (evaluation branch).toRingHom) (evaluation_surjective branch)
  haveI : IsImmersion (point branch) := by unfold point;infer_instance
  haveI : IsFinite (Scheme.TwoAffineOpenCover.specMap ℚ residueField) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI : IsProper (point branch ≫ ThetaLiteralModels.dToBase ℚ) := by
    simpa only [point_over] using
      (inferInstance : IsProper (Scheme.TwoAffineOpenCover.specMap ℚ residueField))
  letI := IsProper.of_comp (point branch) (ThetaLiteralModels.dToBase ℚ)
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance,inferInstance⟩

end FourCorner.ThetaQuadraticInfinityQQ
