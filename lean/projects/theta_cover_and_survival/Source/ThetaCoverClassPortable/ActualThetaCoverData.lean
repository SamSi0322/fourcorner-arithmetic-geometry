import ThetaCoverClassPortable.ActualDQQRepresentation
import ThetaCoverClassPortable.ActualQQCoverPointOD
import ThetaCoverClassPortable.ActualOriginalCoverComparisons
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.RelPicard.BaseChange AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra GoodReductionJacobian
namespace FourCorner.ActualThetaCoverData
open ThetaLiteralModels
abbrev J := ActualDQQRepresentation.designation
def representation := ActualQQCoverPointGroup.repAtCoverOrigin ActualDQQRepresentation.represents
abbrev point := ActualQQCoverPointGroup.coverPoint representation
abbrev law := ActualQQCoverPointGroup.groupLaw representation

def scalarRepresentation (S : Type) [CommRing S] [Algebra ℚ S] :
    RepresentsRelSubPic (baseChange ℚ (dToBase ℚ) S) (sectionBaseChange S ThetaQQRigidifiedLine.origin)
      (algEquivZeroCut (baseChange ℚ (dToBase ℚ) S) (sectionBaseChange S ThetaQQRigidifiedLine.origin))
      (J.baseChange S) :=
  (AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange
    ℚ (dToBase ℚ) ThetaQQRigidifiedLine.origin J representation S).choose

theorem scalarPoincare (S : Type) [CommRing S] [Algebra ℚ S] :
    Nonempty ((scalarRepresentation S).poincare.L ≅
      (BaseChange.ofR (dToBase ℚ) ThetaQQRigidifiedLine.origin S
        (representation.poincare.pullbackAlong
          ⟨pullback.fst J.toBase (specMap ℚ S),pullback.condition⟩)).L) :=
  (AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange
    ℚ (dToBase ℚ) ThetaQQRigidifiedLine.origin J representation S).choose_spec

def originalFMD : FiniteMapData (dToBase ℚ) ThetaQQRigidifiedLine.origin := by
  rw [←ActualQQCoverPointGroup.original_origin_eq]
  exact DRationalInputs.actual_finiteMapData 0

def geometricFMD : FiniteMapData ThetaDGeometricModel.toBase
    (sectionBaseChange ThetaDGeometricModel.K ThetaQQRigidifiedLine.origin) :=
  originalFMD.baseChange ThetaDGeometricModel.K

instance geometricGI : GeometricallyIntegral ThetaDGeometricModel.toBase := by
  letI : GeometricallyIntegral (dToBase ℚ) := DRationalInputs.geometricallyIntegral
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- All geometric comparison inputs are now actual derived data, not hypotheses. -/
def geometric_delta :=
  ActualGeometricCoverDeltaComparison.classifiedCoverPoint_geometric_delta
    J representation geometricFMD (scalarRepresentation ThetaDGeometricModel.K)
      (scalarPoincare ThetaDGeometricModel.K)

/-- The quadratic comparison likewise has no representation/base-change input. -/
def quadratic_native_class :=
  ActualGeometricCoverDeltaComparison.classifiedCoverPoint_quadratic_native_class
    J representation (scalarRepresentation ThetaQuadraticCurve.F)
      (scalarPoincare ThetaQuadraticCurve.F)

end FourCorner.ActualThetaCoverData
