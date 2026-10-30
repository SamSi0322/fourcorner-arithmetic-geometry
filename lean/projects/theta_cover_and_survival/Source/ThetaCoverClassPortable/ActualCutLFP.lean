import ThetaCoverClassPortable.ActualCutSurjectivity
import ThetaCoverClassPortable.ActualLFPInjectivity

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
universe u
namespace FourCorner.ActualCutLFP

theorem finite_stage_injective_and_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε) :
    AffineLimit.IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) ∧
      AffineLimit.IsLFPSurj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) :=
  ⟨ActualLFPInjectivity.algEquivZeroCut_of_twoAffineOpenCover R F.twoAffineOpenCover c ε,
    ActualCutSurjectivity.solution R c ε F⟩

#print axioms finite_stage_injective_and_surjective
end FourCorner.ActualCutLFP
