import ThetaCoverClassPortable.ActualThetaCoverData
import ThetaCoverClassPortable.ActualDQQDictionary
import ThetaCoverClassPortable.ThetaCoverNormalization
import ThetaCoverClassPortable.ThetaCoverGeometryClassAssembly
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj
namespace FourCorner.ThetaCoverClassFullStatement
open ThetaLiteralModels ActualThetaCoverData
local instance : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : Surjective (ThetaProjection.projection (k:=ℚ)) := ThetaProjectionDegree.projection_surjective
local instance (U : (D ℚ).Opens) [Nonempty U] : Nonempty (ThetaCoverActualIntegralClosure.pi ⁻¹ᵁ U) :=
  ThetaCoverActualIntegralClosure.preimage_nonempty U
local instance : Algebra ThetaCoverNativeChartFields.targetField ThetaCoverNativeChartFields.sourceField :=
  (ThetaNativeFunctionFieldMap.fieldMap (ThetaProjection.projection (k:=ℚ))).toAlgebra

/-- The literal normalization assertion on original C,D,pi and every affine. -/
def LiteralNormalization : Prop :=
    IsFinite (ThetaProjection.projection (k:=ℚ)) ∧ Etale (ThetaProjection.projection (k:=ℚ)) ∧
    ThetaCoverNativeQuadraticField.actualV^2=
      algebraMap ThetaCoverNativeChartFields.targetField ThetaCoverNativeChartFields.sourceField ThetaCoverRationalData.rationalH ∧
    Algebra.adjoin ThetaCoverNativeChartFields.targetField
      ({ThetaCoverNativeQuadraticField.actualV}:Set ThetaCoverNativeChartFields.sourceField)=⊤ ∧
    Nonempty (ThetaQuadraticKernel.Q ThetaCoverRationalData.rationalH ≃ₐ[ThetaCoverNativeChartFields.targetField]
      ThetaCoverNativeChartFields.sourceField) ∧
    ThetaCoverNativeQuadraticField.original_quadratic_field_equiv.toRingHom.comp
      (algebraMap ThetaCoverNativeChartFields.targetField (ThetaQuadraticKernel.Q ThetaCoverRationalData.rationalH))=
      ThetaNativeFunctionFieldMap.fieldMap (ThetaProjection.projection (k:=ℚ)) ∧
    (Spec.map (CommRingCat.ofHom (ThetaNativeFunctionFieldMap.fieldMap (ThetaProjection.projection (k:=ℚ)))) ≫
      (D ℚ).fromSpecStalk (genericPoint (D ℚ))=
      (C ℚ).fromSpecStalk (genericPoint (C ℚ)) ≫ ThetaProjection.projection) ∧
    (∀ (U : (D ℚ).Opens) (hU : IsAffineOpen U) [Nonempty U],
      letI := ThetaCoverActualIntegralClosure.affineSectionsAlgebra U
      letI := ThetaCoverActualIntegralClosure.affineFieldAlgebra U
      IsIntegralClosure Γ(C ℚ,ThetaCoverActualIntegralClosure.pi ⁻¹ᵁ U) Γ(D ℚ,U) (C ℚ).functionField)

section Geometric
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : Algebra ThetaDGeometricModel.K ThetaDGeometricModel.field := ThetaDGeometricModel.fieldAlgebra
local instance : IsCurveOver ThetaDGeometricModel.K ThetaDGeometricModel.field := ThetaDGeometricModel.field_isCurveOver
local instance : Algebra.EssFiniteType ThetaDGeometricModel.K ThetaDGeometricModel.field := ThetaDGeometricModel.field_essFiniteType

def GeometricDelta : Prop :=
    let hK := scalarRepresentation ThetaDGeometricModel.K
    letI := (show RepresentsRelSubPic ThetaDGeometricModel.toBase
      (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)
      (algEquivZeroGroupCut ThetaDGeometricModel.toBase
        (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)).toSubPicCondition
      (J.baseChange ThetaDGeometricModel.K) from hK).grpObj
    ∃ (M : CurveModel ThetaDGeometricModel.K ThetaDGeometricModel.field)
      (i : ThetaDGeometricModel.geometricD ≅ M.C),
      i.hom ≫ M.toBase=ThetaDGeometricModel.toBase ∧
      ThetaDGeometricModel.geometricD.fromSpecStalk (genericPoint ThetaDGeometricModel.geometricD) ≫ i.hom=
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ M.C.fromSpecStalk (genericPoint M.C) ∧
      ∃ pts : Pic0 ThetaDGeometricModel.K ThetaDGeometricModel.field ≃
        (Over.mk (𝟙 (Spec (.of ThetaDGeometricModel.K))) ⟶ Over.mk (J.baseChange ThetaDGeometricModel.K).toBase),
        (∀ a b,pts (a+b)=pts a*pts b) ∧ pts ThetaCoverPic0.delta=
          schemeHomOverToOverHom (ActualGeometricCoverDeltaComparison.scalarPoint
            (dToBase ℚ) J ThetaDGeometricModel.K point)

def GeometricWeilClass : Prop :=
    (ThetaCoverPic0.zeroDegreeDivisor : Divisor ThetaDGeometricModel.K ThetaDGeometricModel.field)=
      ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum ∧
    ThetaCoverPic0.delta=Pic0.mk ThetaCoverPic0.zeroDegreeDivisor ∧
    DivisorPicClassification.principalDivisor ThetaCoverFunctions.h ThetaCoverFunctions.h_ne_zero=
      2 • ThetaCoverBoundaryPoints.boundarySum-2 • ThetaDCanonicalInfinityDivisor.infinitySum ∧
    ThetaCoverPic0.delta≠0 ∧ (2:ℕ) • ThetaCoverPic0.delta=0 ∧
    ThetaCoverPic0.delta=Pic0.mk ThetaCoverPic0.contactZeroDegreeDivisor
end Geometric

section Quadratic
local instance : IsIntegral ThetaQuadraticCurve.curve := ThetaQuadraticCurve.curve_integral
local instance : IsProper ThetaQuadraticCurve.toBase := ThetaQuadraticCurve.curve_proper
local instance : SmoothOfRelativeDimension 1 ThetaQuadraticCurve.toBase := ThetaQuadraticCurve.curve_smooth
local instance : Algebra ThetaQuadraticCurve.F ThetaQuadraticCurve.functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsCurveOver ThetaQuadraticCurve.F ThetaQuadraticCurve.functionField := ThetaQuadraticCurve.field_isCurveOver
local instance : Algebra.EssFiniteType ThetaQuadraticCurve.F ThetaQuadraticCurve.functionField := ThetaQuadraticCurve.field_essFiniteType

def QuadraticClass : Prop :=
    Nonempty ((Scheme.Modules.pullback (toProdSpec ThetaQuadraticCurve.toBase)).obj
      ((scalarRepresentation ThetaQuadraticCurve.F).poincare.pullbackAlong
        (ActualGeometricCoverDeltaComparison.scalarPoint (dToBase ℚ) J ThetaQuadraticCurve.F point)).L ≅
          ThetaQuadraticCartierBaseChange.L) ∧
    RigidifiedLineBundle.classesMap ThetaQuadraticPicardClassBaseChange.coefficientChange
      ThetaQQCoverLineEndpoint.rationalPicardClass=ThetaQuadraticCartierWeilNative.rationalPicardClass ∧
    ThetaQuadraticNativeClasses.delta2=ThetaQuadraticContactPlaces.contactClass ∧
    ThetaQuadraticField.h2=(ThetaQuadraticField.ellPlus2/ThetaQuadraticField.ellMinus2)*ThetaQuadraticField.squareMultiplier2^2 ∧
    ∀ (x : closedPoints ThetaQuadraticCurve.curve) (i : ThetaQQUnitRootOpens.NonemptyIndex),
      x.val∈ThetaQuadraticCartierBaseChange.V i →
      (ThetaQuadraticBoundary.E2-ThetaQuadraticInfinityScheme.H2)
        (SmoothProperClosedPointPlaces.placeOfClosedPoint ThetaQuadraticCurve.toBase x)=
      (SmoothProperClosedPointPlaces.placeOfClosedPoint ThetaQuadraticCurve.toBase x).ord
        (ThetaQuadraticCartierWeilNative.localEquation i)
end Quadratic

/-- Full original proposition on the actual QQ representer and actual cover point.
Every base-change representation, Poincare map, FMD and GI input is constructed. -/
theorem prop_theta_cover_class :
    LiteralNormalization ∧
    Nonempty (RepresentsRelSubPic (dToBase ℚ) ThetaQQRigidifiedLine.origin
      (algEquivZeroCut (dToBase ℚ) ThetaQQRigidifiedLine.origin) J) ∧
    Smooth J.toBase ∧ IsProper J.toBase ∧ GeometricallyConnected J.toBase ∧
    AbelianSchemePropertyBundle ℚ J.toBase ∧
    (law.one (𝟙 (Spec (.of ℚ)))).val=J.zeroSection ∧
    (∀ {T : Scheme} (t : T ⟶ Spec (.of ℚ)) (x y : SchemeHomOver t J.toBase),law.mul t x y=law.mul t y x) ∧
    point.val≠J.zeroSection ∧ point≠law.one (𝟙 (Spec (.of ℚ))) ∧
    law.mul (𝟙 (Spec (.of ℚ))) point point=law.one (𝟙 (Spec (.of ℚ))) ∧
    (representation.representableBy.homEquiv (schemeHomOverToOverHom point))=
      ThetaCoverAlgEquivZero.rationalSubPicardClass ∧
    GeometricWeilClass ∧ GeometricDelta ∧ QuadraticClass := by
  refine ⟨ThetaCoverNormalization.actual_literal_normalization,⟨representation⟩,
    ActualDQQRepresentation.smooth,ActualDQQRepresentation.proper,ActualDQQRepresentation.geometricallyConnected,
    ActualDQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose_spec.1,
    ActualQQCoverPointGroup.groupLaw_one representation,
    ActualQQCoverPointGroup.groupLaw_commutative representation,
    ActualQQCoverPointGroup.coverPoint_ne_zeroSection representation,
    ActualQQCoverPointGroup.coverPoint_ne_one representation,
    ActualQQCoverPointGroup.coverPoint_mul_self representation,
    ActualQQCoverPointGroup.coverPoint_class representation,?_,?_,?_⟩
  · exact ⟨rfl,rfl,ThetaCoverDivisor.actual_divisor_h,ThetaCoverPic0.delta_ne_zero,
      ThetaCoverPic0.delta_two_torsion,ThetaCoverPic0.delta_eq_actual_contacts⟩
  · exact ActualThetaCoverData.geometric_delta
  · exact ActualThetaCoverData.quadratic_native_class
end FourCorner.ThetaCoverClassFullStatement
