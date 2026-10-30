import ThetaCoverClassPortable.ActualPoincareScalarNaturality
import ThetaCoverClassPortable.ActualGeometricCoverDeltaDictionary
import ThetaCoverClassPortable.ThetaCoverAlgEquivZero
import ThetaCoverClassPortable.ThetaQQRigidifiedLine
import ThetaCoverClassPortable.ThetaQuadraticPicardClassBaseChange
import ThetaCoverClassPortable.ThetaQuadraticContactClassIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.BaseChange AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj
namespace FourCorner.ActualGeometricCoverDeltaComparison
open ThetaLiteralModels

variable (J : RelativePic0Designation ℚ (dToBase ℚ))
    (h : RepresentsRelSubPic (dToBase ℚ) ThetaQQRigidifiedLine.origin
      (algEquivZeroCut (dToBase ℚ) ThetaQQRigidifiedLine.origin) J)

/-- The original QQ point is its actual universal-property classifier. -/
def classifiedCoverPoint : SchemeHomOver (𝟙 (Spec (.of ℚ))) J.toBase :=
  h.classify (𝟙 (Spec (.of ℚ))) ThetaQQRigidifiedLine.rigidifiedLine ThetaCoverAlgEquivZero.cut_membership

theorem classifiedCoverPoint_poincare :
    Nonempty ((h.poincare.pullbackAlong (classifiedCoverPoint J h)).L ≅ ThetaQQRigidifiedLine.relativeLine) :=
  h.classify_spec _ _ ThetaCoverAlgEquivZero.cut_membership

/-- The literal classifier over every scalar algebra has the actual scalar
pullback of the same QQ cover line as its Poincare fibre. -/
theorem classifiedCoverPoint_scalar_poincare
    (S : Type) [CommRing S] [Algebra ℚ S]
    (hS : RepresentsRelSubPic (baseChange ℚ (dToBase ℚ) S) (sectionBaseChange S ThetaQQRigidifiedLine.origin)
      (algEquivZeroCut (baseChange ℚ (dToBase ℚ) S) (sectionBaseChange S ThetaQQRigidifiedLine.origin)) (J.baseChange S))
    (hP : Nonempty (hS.poincare.L ≅ (BaseChange.ofR (dToBase ℚ) ThetaQQRigidifiedLine.origin S
      (h.poincare.pullbackAlong ⟨pullback.fst J.toBase (specMap ℚ S),pullback.condition⟩)).L)) :
    Nonempty ((Scheme.Modules.pullback (identityPullbackLift (baseChange ℚ (dToBase ℚ) S))).obj
      (hS.poincare.pullbackAlong (scalarPoint (dToBase ℚ) J S (classifiedCoverPoint J h))).L ≅
      (Scheme.Modules.pullback (pullback.fst (dToBase ℚ) (specMap ℚ S))).obj ThetaQQKummerLine.L) :=
  scalarPoint_poincare_line (dToBase ℚ) J S ThetaQQRigidifiedLine.origin h (classifiedCoverPoint J h)
    ThetaQQKummerLine.L (classifiedCoverPoint_poincare J h) hS hP

/-- Exact geometric comparison for the actual original QQ point. -/
theorem classifiedCoverPoint_geometric_poincare
    (hK : RepresentsRelSubPic (baseChange ℚ (dToBase ℚ) ThetaDGeometricModel.K)
      (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)
      (algEquivZeroCut (baseChange ℚ (dToBase ℚ) ThetaDGeometricModel.K)
        (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)) (J.baseChange ThetaDGeometricModel.K))
    (hP : Nonempty (hK.poincare.L ≅ (BaseChange.ofR (dToBase ℚ) ThetaQQRigidifiedLine.origin ThetaDGeometricModel.K
      (h.poincare.pullbackAlong ⟨pullback.fst J.toBase (specMap ℚ ThetaDGeometricModel.K),pullback.condition⟩)).L)) :
    Nonempty ((Scheme.Modules.pullback (toProdSpec ThetaDGeometricModel.toBase)).obj
      (hK.poincare.pullbackAlong
        (scalarPoint (dToBase ℚ) J ThetaDGeometricModel.K (classifiedCoverPoint J h))).L ≅ ThetaGeometricKummerLine.L) :=
  classifiedCoverPoint_scalar_poincare J h ThetaDGeometricModel.K hK hP

/-- The true scalar extension of the original QQ point equals delta in the
native geometric Pic0 dictionary; all curve/model/scalar identities remain literal. -/
theorem classifiedCoverPoint_geometric_delta
    [GeometricallyIntegral ThetaDGeometricModel.toBase]
    (𝔉 : SmoothProperCurve.FiniteMapData ThetaDGeometricModel.toBase
      (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin))
    (hK : RepresentsRelSubPic ThetaDGeometricModel.toBase
      (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)
      (algEquivZeroCut ThetaDGeometricModel.toBase
        (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)) (J.baseChange ThetaDGeometricModel.K))
    (hP : Nonempty (hK.poincare.L ≅ (BaseChange.ofR (dToBase ℚ) ThetaQQRigidifiedLine.origin ThetaDGeometricModel.K
      (h.poincare.pullbackAlong ⟨pullback.fst J.toBase (specMap ℚ ThetaDGeometricModel.K),pullback.condition⟩)).L)) :
    letI := (show RepresentsRelSubPic ThetaDGeometricModel.toBase
      (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)
      (algEquivZeroGroupCut ThetaDGeometricModel.toBase
        (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin)).toSubPicCondition
      (J.baseChange ThetaDGeometricModel.K) from hK).grpObj
    letI := ThetaDGeometricModel.geometric_integral
    letI := ThetaDGeometricModel.fieldAlgebra
    ∃ (M : CurveModel ThetaDGeometricModel.K ThetaDGeometricModel.field)
      (i : ThetaDGeometricModel.geometricD ≅ M.C),
      i.hom ≫ M.toBase=ThetaDGeometricModel.toBase ∧
      ThetaDGeometricModel.geometricD.fromSpecStalk (genericPoint ThetaDGeometricModel.geometricD) ≫ i.hom=
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ M.C.fromSpecStalk (genericPoint M.C) ∧
      ∃ pts : Pic0 ThetaDGeometricModel.K ThetaDGeometricModel.field ≃
        (Over.mk (𝟙 (Spec (.of ThetaDGeometricModel.K))) ⟶ Over.mk (J.baseChange ThetaDGeometricModel.K).toBase),
        (∀ a b,pts (a+b)=pts a*pts b) ∧ pts ThetaCoverPic0.delta=
          schemeHomOverToOverHom (scalarPoint (dToBase ℚ) J ThetaDGeometricModel.K (classifiedCoverPoint J h)) :=
  exists_actual_geometric_delta_dictionary _ 𝔉 (J.baseChange ThetaDGeometricModel.K) hK _
    (classifiedCoverPoint_geometric_poincare J h hK hP)

/-- Over the actual quadratic coefficient field the comparison is an actual
Poincare line isomorphism. No algebraically closed Pic0 dictionary is assumed. -/
theorem classifiedCoverPoint_quadratic_poincare
    (hF : RepresentsRelSubPic (baseChange ℚ (dToBase ℚ) ThetaQuadraticCurve.F)
      (sectionBaseChange ThetaQuadraticCurve.F ThetaQQRigidifiedLine.origin)
      (algEquivZeroCut (baseChange ℚ (dToBase ℚ) ThetaQuadraticCurve.F)
        (sectionBaseChange ThetaQuadraticCurve.F ThetaQQRigidifiedLine.origin)) (J.baseChange ThetaQuadraticCurve.F))
    (hP : Nonempty (hF.poincare.L ≅ (BaseChange.ofR (dToBase ℚ) ThetaQQRigidifiedLine.origin ThetaQuadraticCurve.F
      (h.poincare.pullbackAlong ⟨pullback.fst J.toBase (specMap ℚ ThetaQuadraticCurve.F),pullback.condition⟩)).L)) :
    Nonempty ((Scheme.Modules.pullback (toProdSpec ThetaQuadraticCurve.toBase)).obj
      (hF.poincare.pullbackAlong
        (scalarPoint (dToBase ℚ) J ThetaQuadraticCurve.F (classifiedCoverPoint J h))).L ≅ ThetaQuadraticCartierBaseChange.L) :=
  classifiedCoverPoint_scalar_poincare J h ThetaQuadraticCurve.F hF hP

section QuadraticNativeClass
local instance : IsIntegral ThetaQuadraticCurve.curve := ThetaQuadraticCurve.curve_integral
local instance : IsProper ThetaQuadraticCurve.toBase := ThetaQuadraticCurve.curve_proper
local instance : SmoothOfRelativeDimension 1 ThetaQuadraticCurve.toBase := ThetaQuadraticCurve.curve_smooth
local instance : Algebra ThetaQuadraticCurve.F ThetaQuadraticCurve.functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsCurveOver ThetaQuadraticCurve.F ThetaQuadraticCurve.functionField := ThetaQuadraticCurve.field_isCurveOver
local instance : Algebra.EssFiniteType ThetaQuadraticCurve.F ThetaQuadraticCurve.functionField := ThetaQuadraticCurve.field_essFiniteType

/-- Single-point native quadratic class comparison: actual Poincare fibre,
actual relative-Picard scalar map, every native Weil coefficient, contact
class, and the original coefficient-sensitive function identity. -/
theorem classifiedCoverPoint_quadratic_native_class
    (hF : RepresentsRelSubPic (baseChange ℚ (dToBase ℚ) ThetaQuadraticCurve.F)
      (sectionBaseChange ThetaQuadraticCurve.F ThetaQQRigidifiedLine.origin)
      (algEquivZeroCut (baseChange ℚ (dToBase ℚ) ThetaQuadraticCurve.F)
        (sectionBaseChange ThetaQuadraticCurve.F ThetaQQRigidifiedLine.origin)) (J.baseChange ThetaQuadraticCurve.F))
    (hP : Nonempty (hF.poincare.L ≅ (BaseChange.ofR (dToBase ℚ) ThetaQQRigidifiedLine.origin ThetaQuadraticCurve.F
      (h.poincare.pullbackAlong ⟨pullback.fst J.toBase (specMap ℚ ThetaQuadraticCurve.F),pullback.condition⟩)).L)) :
    Nonempty ((Scheme.Modules.pullback (toProdSpec ThetaQuadraticCurve.toBase)).obj
      (hF.poincare.pullbackAlong
        (scalarPoint (dToBase ℚ) J ThetaQuadraticCurve.F (classifiedCoverPoint J h))).L ≅ ThetaQuadraticCartierBaseChange.L) ∧
    RigidifiedLineBundle.classesMap ThetaQuadraticPicardClassBaseChange.coefficientChange
      ThetaQQCoverLineEndpoint.rationalPicardClass=ThetaQuadraticCartierWeilNative.rationalPicardClass ∧
    ThetaQuadraticNativeClasses.delta2=ThetaQuadraticContactPlaces.contactClass ∧
    ThetaQuadraticField.h2=(ThetaQuadraticField.ellPlus2/ThetaQuadraticField.ellMinus2)*ThetaQuadraticField.squareMultiplier2^2 ∧
    ∀ (x : closedPoints ThetaQuadraticCurve.curve) (i : ThetaQQUnitRootOpens.NonemptyIndex),
      x.val∈ThetaQuadraticCartierBaseChange.V i →
      (ThetaQuadraticBoundary.E2-ThetaQuadraticInfinityScheme.H2)
        (SmoothProperClosedPointPlaces.placeOfClosedPoint ThetaQuadraticCurve.toBase x)=
      (SmoothProperClosedPointPlaces.placeOfClosedPoint ThetaQuadraticCurve.toBase x).ord
        (ThetaQuadraticCartierWeilNative.localEquation i) :=
  ⟨classifiedCoverPoint_quadratic_poincare J h hF hP,
    ThetaQuadraticPicardClassBaseChange.actual_classesMap,
    ThetaQuadraticContactClassIdentity.delta2_eq_contactClass,
    ThetaQuadraticField.exact_quadratic_identity,
    ThetaQuadraticCartierWeilNative.actual_Weil_order⟩
end QuadraticNativeClass

end FourCorner.ActualGeometricCoverDeltaComparison
