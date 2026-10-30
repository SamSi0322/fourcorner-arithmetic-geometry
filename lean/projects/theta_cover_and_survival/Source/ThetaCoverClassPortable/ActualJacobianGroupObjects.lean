import ThetaCoverClassPortable.NativeSurvivalClosedBoundary
import ThetaCoverClassPortable.ActualCQQDictionary
import ThetaCoverClassPortable.ActualDQQDictionary
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ThetaCoverClassPortable.SmoothIntegralCharts
import ThetaCoverClassPortable.ThetaOriginImage
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
namespace FourCorner.ThetaSurvivingActualJacobians
open ThetaSurvivingNativeRealPath ThetaSurvivingNativeApplication
open ThetaLocalSurvival.Multiplication

theorem geometricallyIntegral_of_smooth_connected_section {J : Scheme} (j : J ⟶ base)
    (hs : Smooth j) (hc : GeometricallyConnected j) (z : base ⟶ J) (hz : z≫j=𝟙 _) :
    GeometricallyIntegral j := by
  letI := hs
  letI := hc
  constructor
  intro K _ y Z fst snd hpb
  let zi : Spec (.of K) ⟶ pullback j y := pullback.lift (y≫z) (𝟙 _) (by simp [Category.assoc,hz])
  have hzi : zi≫pullback.snd j y=𝟙 _ := by simp [zi]
  haveI : IsIntegral (pullback j y) := isIntegral_of_smooth_of_geometricallyConnected K
    (pullback.snd j y) inferInstance inferInstance zi hzi
  exact IsIntegral.of_isIso hpb.isoPullback.inv

abbrev JC : Over base := Over.mk ActualCQQRepresentation.designation.toBase
abbrev JD : Over base := Over.mk ActualDQQRepresentation.designation.toBase

def cLaw := ActualCQQRepresentation.actual_group_abelJacobi_pic0.choose
def dLaw := ActualDQQRepresentation.actual_group_abelJacobi_pic0.choose
def cAJ := ActualCQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose
def dAJ := ActualDQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose
instance : GrpObj JC := cLaw.grpObjOverMk
instance : GrpObj JD := dLaw.grpObjOverMk
instance : IsCommMonObj JC := cLaw.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr
  ActualCQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose_spec.2.1
instance : IsCommMonObj JD := dLaw.isCommMonObj_grpObjOverMk_iff_mul_comm.mpr
  ActualDQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose_spec.2.1
instance : IsProper JC.hom := ActualCQQRepresentation.proper
instance : IsProper JD.hom := ActualDQQRepresentation.proper
instance : GeometricallyIntegral JC.hom := geometricallyIntegral_of_smooth_connected_section _
  ActualCQQRepresentation.smooth ActualCQQRepresentation.geometricallyConnected
  ActualCQQRepresentation.designation.zeroSection ActualCQQRepresentation.designation.zeroSection_toBase
instance : GeometricallyIntegral JD.hom := geometricallyIntegral_of_smooth_connected_section _
  ActualDQQRepresentation.smooth ActualDQQRepresentation.geometricallyConnected
  ActualDQQRepresentation.designation.zeroSection ActualDQQRepresentation.designation.zeroSection_toBase

def iC : sourceObject ⟶ JC := Over.homMk cAJ.1 (by simpa using cAJ.2)
def iD : Over.mk (ThetaLiteralModels.dToBase ℚ) ⟶ JD := Over.homMk dAJ.1 (by simpa using dAJ.2)
def actualProjection : sourceObject ⟶ Over.mk (ThetaLiteralModels.dToBase ℚ) :=
  Over.homMk (ThetaProjection.projection (k:=ℚ)) (ThetaSourceComparison.rational_base_unique _ _)
def iD_after_projection : sourceObject ⟶ JD := actualProjection≫iD

theorem originalOrigin_iC : originalOrigin≫iC=1 := by
  apply Over.OverMorphism.ext
  have hOne := congrArg Subtype.val (cLaw.overHomToSchemeHomOver_one (𝟙 base))
  change (1 : rationalBase ⟶ JC).left=(cLaw.one (𝟙 base)).1 at hOne
  rw [hOne]
  exact ActualCQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose_spec.2.2.2.1.trans
    ActualCQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose_spec.2.2.1.symm

theorem originalOrigin_iD_after_projection : originalOrigin≫iD_after_projection=1 := by
  apply Over.OverMorphism.ext
  have hOne := congrArg Subtype.val (dLaw.overHomToSchemeHomOver_one (𝟙 base))
  change (1 : rationalBase ⟶ JD).left=(dLaw.one (𝟙 base)).1 at hOne
  rw [hOne]
  change ThetaActualPoints.originC≫ThetaProjection.projection≫dAJ.1=(dLaw.one (𝟙 base)).1
  rw [←Category.assoc,ThetaOriginImage.origin_image]
  exact ActualDQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose_spec.2.2.2.1.trans
    ActualDQQRepresentation.actual_group_abelJacobi_pic0.choose_spec.choose_spec.2.2.1.symm
end FourCorner.ThetaSurvivingActualJacobians
