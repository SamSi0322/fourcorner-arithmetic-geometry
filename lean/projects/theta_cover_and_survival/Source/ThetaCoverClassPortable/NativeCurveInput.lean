import ThetaCoverClassPortable.NativeRealPathPackage
import ThetaCoverClassPortable.ThetaSourceSmooth
import ThetaCoverClassPortable.ThetaSourceGenus
import ThetaCoverClassPortable.ThetaLocalSurvival
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FourCorner.ThetaSurvivingNativeApplication
open ThetaLiteralModels ThetaSurvivingNativeRealPath
theorem source_geometricallyIntegral : GeometricallyIntegral (cToBase ℚ) := by
  haveI := OppositeProjective.ExactGenus.geometricallyIntegral (1:ℚ) 5
    (by norm_num) (by norm_num) (by norm_num)
  constructor
  intro L _ y Z fst snd hpb
  haveI := GeometricallyIntegral.geometrically_isIntegral (f:=ThetaSourceGenus.oppositeBase) y
    (CategoryTheory.Limits.pullback.fst ThetaSourceGenus.oppositeBase y)
    (CategoryTheory.Limits.pullback.snd ThetaSourceGenus.oppositeBase y) (.of_hasPullback _ _)
  haveI : IsIntegral (CategoryTheory.Limits.pullback (cToBase ℚ) y) :=
    IsIntegral.of_isIso (ThetaSourceGenus.baseChangeIso y).inv
  exact IsIntegral.of_isIso hpb.isoPullback.inv
instance : IsProper sourceObject.hom := c_proper ℚ
instance : SmoothOfRelativeDimension 1 sourceObject.hom := ThetaSourceSmooth.source_smooth
instance : GeometricallyIntegral sourceObject.hom := source_geometricallyIntegral
end FourCorner.ThetaSurvivingNativeApplication
