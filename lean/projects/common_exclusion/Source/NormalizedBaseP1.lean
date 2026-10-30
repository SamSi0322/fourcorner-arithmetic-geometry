import ProperCurveFieldIsoQ
import ProjectiveLineField
import NormalizedModelCover

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.NormalizedBaseP1
local instance p1Integral : IsIntegral (ProjectiveLineCharts.P1 ℚ) := ProjectiveLineCharts.integral ℚ

abbrev baseCurve {K : Type} [Field K] [CharZero K] := (NormalizedModelCover.baseModel K).C
abbrev baseToBase {K : Type} [Field K] [CharZero K] := (NormalizedModelCover.baseModel K).toBase
abbrev baseFFEquiv {K : Type} [Field K] [CharZero K] := (NormalizedModelCover.baseModel K).ffEquiv

/-- The field identification uses the original rational function X on both genuine models. -/
def fieldEquiv :
    letI := ProjectiveLineCharts.integral ℚ
    (baseCurve (K := ℚ)).functionField ≃+* (ProjectiveLineCharts.P1 ℚ).functionField :=
  letI := ProjectiveLineCharts.integral ℚ
  baseFFEquiv.symm.trans (ProjectiveLineCharts.fieldEquiv ℚ)

/-- The actual normalization model of Q(X) is isomorphic to the literal standard Proj P1. -/
def iso : baseCurve (K := ℚ) ≅ ProjectiveLineCharts.P1 ℚ := by
  letI := ProjectiveLineCharts.integral ℚ
  letI := ProjectiveLineCharts.proper ℚ
  letI := ProjectiveLineCharts.smooth ℚ
  exact ProperCurveFieldIsoQ.iso (baseToBase (K := ℚ)) (ProjectiveLineCharts.toBase ℚ) fieldEquiv

lemma generic_iso :
    (baseCurve (K := ℚ)).fromSpecStalk (genericPoint (baseCurve (K := ℚ))) ≫ iso.hom =
      Spec.map (CommRingCat.ofHom fieldEquiv.symm.toRingHom) ≫
        (ProjectiveLineCharts.P1 ℚ).fromSpecStalk (genericPoint (ProjectiveLineCharts.P1 ℚ)) := by
  letI := ProjectiveLineCharts.integral ℚ
  letI := ProjectiveLineCharts.proper ℚ
  letI := ProjectiveLineCharts.smooth ℚ
  exact ProperCurveFieldIsoQ.generic_forward (baseToBase (K := ℚ)) (ProjectiveLineCharts.toBase ℚ) fieldEquiv

end FourCorner.NormalizedBaseP1
#print axioms FourCorner.NormalizedBaseP1.iso
#print axioms FourCorner.NormalizedBaseP1.generic_iso
