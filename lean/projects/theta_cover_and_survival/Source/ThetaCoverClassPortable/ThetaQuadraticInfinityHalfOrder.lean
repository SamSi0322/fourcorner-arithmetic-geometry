import ThetaCoverClassPortable.ThetaQuadraticInfinityDistinct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct

namespace FourCorner.ThetaQuadraticInfinityHalfOrder
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticPlacePullback
open ThetaQuadraticHalfDivisor ThetaQuadraticHalfUnweighted
abbrev K := ThetaDGeometricModel.K
local instance : Algebra F K := coefficientEmbedding.toRingHom.toAlgebra
local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : IsProper ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_proper
local instance : SmoothOfRelativeDimension 1 ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_smooth
local instance : Algebra K ThetaDGeometricModel.field := ThetaDGeometricModel.fieldAlgebra

abbrev L := ThetaQuadraticInfinityScheme.residueField
abbrev Lq := ThetaQuadraticInfinityQQ.residueField

def root : K := Classical.choose (IsAlgClosed.exists_pow_nat_eq (-2:K) (by decide : 0<2))
theorem root_sq : root^2=(-2:K) := Classical.choose_spec
  (IsAlgClosed.exists_pow_nat_eq (-2:K) (by decide : 0<2))
def embedding : L →ₐ[F] K := QuadraticAlgebra.lift ⟨root,by
  rw [←pow_two,root_sq]
  simp only [Algebra.smul_def,map_neg,map_ofNat,map_zero,zero_mul,add_zero]
  exact (mul_one _).symm⟩
def rationalInclusion : Lq →+* L :=
  ThetaQuadraticInfinityScheme.tensorEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : Lq →ₐ[ℚ] F ⊗[ℚ] Lq).toRingHom

theorem point_original (b : Bool) :
    ThetaQuadraticInfinityScheme.point b ≫ toRational =
    Spec.map (CommRingCat.ofHom rationalInclusion) ≫ ThetaQuadraticInfinityQQ.point b := by
  simp only [ThetaQuadraticInfinityScheme.point,Category.assoc]
  rw [←pullback.condition]
  have hf : (ThetaQuadraticInfinityScheme.fibreIso b).inv ≫
      pullback.fst (ThetaQuadraticInfinityQQ.point b) toRational =
      pullback.fst ThetaQuadraticInfinityScheme.rationalBaseMap baseMap := by
    simp [ThetaQuadraticInfinityScheme.fibreIso]
  rw [←Category.assoc (ThetaQuadraticInfinityScheme.fibreIso b).inv, hf]
  simp only [Category.assoc,ThetaQuadraticInfinityScheme.specTensorIso,Iso.trans_hom,
    Iso.symm_hom,pullbackSymmetry_hom_comp_fst_assoc,pullbackSpecIso_inv_snd_assoc]
  change Spec.map (CommRingCat.ofHom ThetaQuadraticInfinityScheme.tensorEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Lq →ₐ[ℚ] F ⊗[ℚ] Lq).toRingHom) ≫ _ = _
  rw [←Spec.map_comp_assoc]
  rfl

def rawPoint (b : Bool) : Spec (.of K) ⟶ curve :=
  Spec.map (CommRingCat.ofHom embedding.toRingHom) ≫ ThetaQuadraticInfinityScheme.point b

theorem rawPoint_over (b : Bool) : rawPoint b ≫ toBase=extensionMap := by
  rw [rawPoint,Category.assoc,ThetaQuadraticInfinityScheme.point_over,←Spec.map_comp]
  congr 1
  ext a
  exact embedding.commutes a

def point (b : Bool) : Spec (.of K) ⟶ ThetaDGeometricModel.geometricD :=
  pullback.lift (rawPoint b) (𝟙 _) (by simpa using rawPoint_over b) ≫ geometricBaseChangeIso.hom

theorem point_over (b : Bool) : point b ≫ ThetaDGeometricModel.toBase=𝟙 _ := by
  simp [point,Category.assoc]
theorem point_source (b : Bool) : point b ≫ geometricProjection=rawPoint b := by
  simp [point,Category.assoc,ThetaQuadraticGeometricContacts.iso_geometricProjection]

local instance : IsScalarTower ℚ F K :=
  IsScalarTower.of_algebraMap_eq (fun q => (coefficientEmbedding.commutes q).symm)
def rationalEmbedding : Lq →ₐ[ℚ] K :=
  (embedding.restrictScalars ℚ).comp
    ((ThetaQuadraticInfinityScheme.tensorEquiv.toAlgHom.restrictScalars ℚ).comp
      Algebra.TensorProduct.includeRight)
def parameter (b : Bool) : K := rationalEmbedding (ThetaQuadraticInfinityQQ.parameter b)
theorem parameter_root (b : Bool) : ThetaDInfinityPoints.polynomial.eval (parameter b)=0 := by
  have h := congrArg rationalEmbedding (ThetaQuadraticInfinityQQ.quartic_relation b)
  simp only [map_add,map_mul,map_pow,map_ofNat,map_zero] at h
  simp only [ThetaDInfinityPoints.polynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one]
  dsimp only [parameter]
  linear_combination h

def infinityParameter (b : Bool) : ThetaDFourInfinityPlaces.Parameters :=
  ⟨parameter b,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots ThetaDInfinityPoints.nonzero).mpr (parameter_root b))⟩

theorem point_is_infinity (b : Bool) :
    point b=ThetaDInfinityPoints.parametrizedPoint (infinityParameter b) := by
  apply pullback.hom_ext
  · have hs : point b ≫ pullback.fst (ThetaLiteralModels.dToBase ℚ) ThetaDGeometricModel.qb =
        Spec.map (CommRingCat.ofHom rationalEmbedding.toRingHom) ≫ ThetaQuadraticInfinityQQ.point b := by
      rw [←geometricProjection_toRational,←Category.assoc,point_source]
      simp only [rawPoint,Category.assoc,point_original,←Spec.map_comp_assoc]
      rfl
    rw [hs]
    simp only [ThetaDInfinityPoints.parametrizedPoint,ThetaDInfinityPoints.point,
      ThetaDGeometricChartPoints.point,pullback.lift_fst]
    change _=ThetaDGeometricChartPoints.toOriginal 0 ![parameter b,0] _
    change Spec.map (CommRingCat.ofHom rationalEmbedding.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (ThetaQuadraticInfinityQQ.evaluation b).toRingHom) ≫
          ThetaDPlaneChartSections.chartMap 0 =
      Spec.map (CommRingCat.ofHom (ThetaDGeometricChartPoints.evaluation 0 ![parameter b,0] (ThetaDInfinityPoints.relations _ (parameter_root b))).toRingHom) ≫
          ThetaDPlaneChartSections.chartMap 0
    rw [←Spec.map_comp_assoc]
    apply congrArg (fun f : Spec (.of K) ⟶ Spec (.of (ThetaDPlaneChartSections.chartRing 0)) =>
      f ≫ ThetaDPlaneChartSections.chartMap 0)
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    change (rationalEmbedding.comp (ThetaQuadraticInfinityQQ.evaluation b)).toRingHom=
      (ThetaDGeometricChartPoints.evaluation 0 ![parameter b,0] (ThetaDInfinityPoints.relations _ (parameter_root b))).toRingHom
    congr 1
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro a
    fin_cases a <;> simp [ThetaQuadraticInfinityQQ.evaluation,ThetaQuadraticInfinityQQ.values,
      ThetaDGeometricChartPoints.evaluation,parameter]
  · rw [point_over]
    exact (ThetaDInfinityPoints.point_over _ _).symm

def closedPoint (b : Bool) : closedPoints ThetaDGeometricModel.geometricD :=
  SchemePointStalkEvaluation.closedPointOfPoint ThetaDGeometricModel.toBase (point b) (point_over b)

theorem geometricPlace_eq (b : Bool) : geometricPlace (closedPoint b)=
    ThetaDFourInfinityPlaces.place (infinityParameter b) := by
  apply congrArg (SmoothProperClosedPointPlaces.placeOfClosedPoint ThetaDGeometricModel.toBase)
  apply Subtype.ext
  exact congrArg (fun f : Spec (.of K) ⟶ ThetaDGeometricModel.geometricD =>
    f (IsLocalRing.closedPoint K)) (point_is_infinity b)

theorem sourcePlace_eq (b : Bool) : sourcePlace (closedPoint b)=ThetaQuadraticInfinityScheme.place b := by
  apply congrArg (SmoothProperClosedPointPlaces.placeOfClosedPoint toBase)
  apply Subtype.ext
  have h := congrArg (fun f : Spec (.of K) ⟶ curve => f (IsLocalRing.closedPoint K)) (point_source b)
  change geometricProjection (point b (IsLocalRing.closedPoint K)) =
    ThetaQuadraticInfinityScheme.point b
      (Spec.map (CommRingCat.ofHom embedding.toRingHom) (IsLocalRing.closedPoint K)) at h
  rw [show Spec.map (CommRingCat.ofHom embedding.toRingHom) (IsLocalRing.closedPoint K)=
    IsLocalRing.closedPoint L from Subsingleton.elim _ _] at h
  exact h

/-- Actual valuation at each displayed quadratic infinity point. -/
theorem half_infinity_neg_one (b : Bool) : halfDivisor (ThetaQuadraticInfinityScheme.place b)= -1 := by
  classical
  have hh := actual_half_pullback_coefficient (closedPoint b)
  rw [sourcePlace_eq,geometricPlace_eq] at hh
  have hH : ThetaDCanonicalInfinityDivisor.infinitySum
      (ThetaDFourInfinityPlaces.place (infinityParameter b))=1 := by
    rw [ThetaDCanonicalInfinityDivisor.infinitySum_apply,if_pos
      ((ThetaDCanonicalInfinityDivisor.mem_infinityPlaces _).mpr ⟨infinityParameter b,rfl⟩)]
  simp only [Finsupp.sub_apply,hH,ThetaCoverBoundaryPoints.boundarySum_apply] at hh
  split_ifs at hh with he
  · obtain ⟨s,hs⟩ := he
    have hb := ThetaQuadraticBoundaryHalfOrder.geometric_boundary_half_one s
    rw [hs] at hb
    have hE : ThetaCoverBoundaryPoints.boundarySum
        (ThetaDFourInfinityPlaces.place (infinityParameter b))=1 := by
      rw [ThetaCoverBoundaryPoints.boundarySum_apply,if_pos ⟨s,hs⟩]
    simp only [Finsupp.sub_apply,hH,hE] at hb
    norm_num at hb
  · norm_num at hh
    exact hh.symm

end FourCorner.ThetaQuadraticInfinityHalfOrder
