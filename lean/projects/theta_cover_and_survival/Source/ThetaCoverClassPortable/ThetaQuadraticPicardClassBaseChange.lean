import ThetaCoverClassPortable.ThetaQuadraticCartierWeilNative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open NeronModelInfra AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
namespace FourCorner.ThetaQuadraticPicardClassBaseChange
open ThetaQuadraticCurve ThetaQuadraticCartierBaseChange ThetaQuadraticCartierWeilNative

/-- The actual coefficient-field extension as an object over Spec QQ. -/
def coefficientChange : SchemeHomOver baseMap (𝟙 (Spec (.of ℚ))) :=
  ⟨baseMap,by simp⟩

abbrev sourceProjection := pullback.fst (ThetaLiteralModels.dToBase ℚ) (𝟙 (Spec (.of ℚ)))
abbrev changeProjection := RelPicard.baseChangeSnd (ThetaLiteralModels.dToBase ℚ) coefficientChange

theorem changeProjection_original : changeProjection ≫ sourceProjection=toRational := by
  simp [changeProjection,sourceProjection,RelPicard.baseChangeSnd,toRational]

/-- Equality under the genuine native relative-Picard presheaf map,
not invariance of a geometric label being treated as descent. -/
theorem actual_classesMap :
    RelPicard.RigidifiedLineBundle.classesMap coefficientChange
      ThetaQQCoverLineEndpoint.rationalPicardClass=rationalPicardClass := by
  apply Quotient.sound
  exact ⟨(Scheme.Modules.pullbackComp changeProjection sourceProjection).app ThetaQQKummerLine.L ≪≫
    (Scheme.Modules.pullbackCongr changeProjection_original).app ThetaQQKummerLine.L⟩

end FourCorner.ThetaQuadraticPicardClassBaseChange
