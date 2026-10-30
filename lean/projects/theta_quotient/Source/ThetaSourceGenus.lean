import ThetaSourceComparison
import ThetaIsoFunctionField
noncomputable section
namespace FourCorner.ThetaSourceGenus
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open ThetaLiteralModels ThetaSourceComparison
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev oppositeBase := OppositeProjective.toBase (1:ℚ) 5
abbrev qb := Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ)

def baseChangeIso {L : Type} [Field L] (y : Spec (.of L) ⟶ Spec (.of ℚ)) :
    pullback (cToBase ℚ) y ≅ pullback oppositeBase y :=
  asIso (pullback.map (cToBase ℚ) y oppositeBase y (sourceIso (k:=ℚ)).hom (𝟙 _) (𝟙 _)
    (by simpa using sourceIso_over.symm) (by simp))

theorem source_connected : GeometricallyConnected (cToBase ℚ) := by
  haveI := OppositeProjective.ExactGenus.geometricallyConnected (1:ℚ) 5
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y=>?_⟩
  haveI : ConnectedSpace ↥(pullback oppositeBase y) :=
    GeometricallyConnected.geometrically_connectedSpace (f:=oppositeBase) y (pullback.fst oppositeBase y) (pullback.snd oppositeBase y) (.of_hasPullback _ _)
  exact (baseChangeIso y).hom.homeomorph.connectedSpace_iff.mpr inferInstance
abbrev geometricScheme := pullback (cToBase ℚ) qb
abbrev geometricToBase := pullback.snd (cToBase ℚ) qb
abbrev geometricIso := baseChangeIso qb

theorem geometric_integral : IsIntegral geometricScheme := by
  haveI := OppositeProjective.ExactGenus.geometricIntegral (1:ℚ) 5
    (by norm_num) (by norm_num) (by norm_num)
  exact IsIntegral.of_isIso geometricIso.inv
lemma geometricIso_over : geometricIso.hom ≫ OppositeProjective.ExactGenus.geometricToBase (1:ℚ) 5 = geometricToBase := by
  simp only [geometricIso,baseChangeIso,asIso_hom,pullback.map,pullback.lift_snd,Category.comp_id]

/-- Genus five of the actual Qbar pullback of the original theta intersection. -/
theorem genus_five :
    letI := geometric_integral
    letI := (baseToFunctionField geometricToBase).toAlgebra
    genusFF (AlgebraicClosure ℚ) geometricScheme.functionField=5 := by
  letI := geometric_integral
  letI := OppositeProjective.ExactGenus.geometricIntegral (1:ℚ) 5
    (by norm_num) (by norm_num) (by norm_num)
  letI := (baseToFunctionField geometricToBase).toAlgebra
  letI := (baseToFunctionField (OppositeProjective.ExactGenus.geometricToBase (1:ℚ) 5)).toAlgebra
  let e := ThetaIsoFunctionField.algEquiv geometricToBase
    (OppositeProjective.ExactGenus.geometricToBase (1:ℚ) 5) geometricIso geometricIso_over
  exact (genusFF_eq_of_algEquiv e).symm.trans
    (OppositeProjective.ExactGenus.geometric_genus_five (1:ℚ) 5
      (by norm_num) (by norm_num) (by norm_num))
end FourCorner.ThetaSourceGenus
#print axioms FourCorner.ThetaSourceGenus.source_connected
#print axioms FourCorner.ThetaSourceGenus.genus_five
