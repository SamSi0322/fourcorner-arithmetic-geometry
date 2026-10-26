import HpLiteralFieldIdentification
import ThetaIsoFunctionField

namespace FourCorner.HpLiteralGeometric
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open HpLiteralProjective
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

 def modelIso (p : ℚ) (hp : 1<p) : curve ℚ p ≅ HpSchemeModel.curve p :=
  (HpLiteralFieldIdentification.literal_model_iso p hp).choose
 theorem modelIso_over (p : ℚ) (hp : 1<p) : (modelIso p hp).hom ≫ HpSchemeModel.toBase p=toBase ℚ p :=
  (HpLiteralFieldIdentification.literal_model_iso p hp).choose_spec

 def baseChangeIso (p : ℚ) (hp : 1<p) {L : Type} [Field L] (y : Spec (.of L) ⟶ Spec (.of ℚ)) :
    pullback (toBase ℚ p) y ≅ pullback (HpSchemeModel.toBase p) y :=
  asIso (pullback.map (toBase ℚ p) y (HpSchemeModel.toBase p) y (modelIso p hp).hom (𝟙 _) (𝟙 _)
    (by simpa using (modelIso_over p hp).symm) (by simp))

abbrev qb := Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ)
abbrev geometricScheme (p : ℚ) := pullback (toBase ℚ p) qb
abbrev geometricToBase (p : ℚ) := pullback.snd (toBase ℚ p) qb
abbrev geometricIso (p : ℚ) (hp : 1<p) := baseChangeIso p hp qb

 theorem geometricIntegral (p : ℚ) (hp : 1<p) : IsIntegral (geometricScheme p) := by
  haveI := HpSchemeModel.geometricIntegral p hp
  exact IsIntegral.of_isIso (geometricIso p hp).inv

 theorem geometricIso_over (p : ℚ) (hp : 1<p) :
    (geometricIso p hp).hom ≫ HpSchemeModel.geometricToBase p=geometricToBase p := by
  simp only [geometricIso,baseChangeIso,asIso_hom,pullback.map,pullback.lift_snd,Category.comp_id]

/-- Actual Qbar function field of the WHOLE literal P4 intersection. -/
 def geometricFieldEquiv (p : ℚ) (hp : 1<p) :
    letI := geometricIntegral p hp
    letI := (baseToFunctionField (geometricToBase p)).toAlgebra
    HpLiteralField.field (AlgebraicClosure ℚ) (p : AlgebraicClosure ℚ) ≃ₐ[AlgebraicClosure ℚ]
      (geometricScheme p).functionField := by
  letI := geometricIntegral p hp
  letI := HpSchemeModel.geometricIntegral p hp
  letI := (baseToFunctionField (geometricToBase p)).toAlgebra
  letI := (baseToFunctionField (HpSchemeModel.geometricToBase p)).toAlgebra
  exact (HpSchemeModel.geometricFieldEquiv p hp).trans
    (ThetaIsoFunctionField.algEquiv (geometricToBase p) (HpSchemeModel.geometricToBase p)
      (geometricIso p hp) (geometricIso_over p hp))

 theorem geometric_genus_five (p : ℚ) (hp : 1<p) :
    letI := geometricIntegral p hp
    letI := (baseToFunctionField (geometricToBase p)).toAlgebra
    genusFF (AlgebraicClosure ℚ) (geometricScheme p).functionField=5 := by
  letI := geometricIntegral p hp
  letI := (baseToFunctionField (geometricToBase p)).toAlgebra
  exact (genusFF_eq_of_algEquiv (geometricFieldEquiv p hp)).symm.trans
    (HpGeometricGenus.rational_geometric_genus_five p hp)

 theorem geometricProper (p : ℚ) : IsProper (geometricToBase p) := by
  haveI := HpLiteralProjective.proper ℚ p
  unfold geometricToBase
  infer_instance

 theorem geometricSmooth (p : ℚ) (hp : 1<p) : SmoothOfRelativeDimension 1 (geometricToBase p) := by
  haveI := HpLiteralSmooth.smooth p (by linarith) (by linarith) (by linarith)
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P:=@SmoothOfRelativeDimension 1) _ _ inferInstance

 theorem geometricallyConnected (p : ℚ) (hp : 1<p) : GeometricallyConnected (toBase ℚ p) := by
  haveI := HpSchemeModel.model_geometricallyConnected p hp
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y=>?_⟩
  haveI : ConnectedSpace ↥(pullback (HpSchemeModel.toBase p) y) :=
    GeometricallyConnected.geometrically_connectedSpace (f:=HpSchemeModel.toBase p) y
      (pullback.fst _ _) (pullback.snd _ _) (.of_hasPullback _ _)
  exact (baseChangeIso p hp y).hom.homeomorph.connectedSpace_iff.mpr inferInstance

/-- Intrinsic genus five of the literal C_p, measured by actual global
relative Kähler differentials on its actual categorical Qbar base change. -/
 theorem geometric_globalDifferentials_five (p : ℚ) (hp : 1<p) :
    let c := geometricToBase p
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤)=5 := by
  let c := geometricToBase p
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
  letI := geometricIntegral p hp
  letI := geometricProper p
  letI := geometricSmooth p hp
  let V := (HpTwoChartCover.cover ℚ p (by linarith)).pullback (toBase ℚ p) (AlgebraicClosure ℚ)
  obtain ⟨hfin,hrank⟩ := KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF V c
  exact ⟨hfin,hrank.trans (geometric_genus_five p hp)⟩

#print axioms modelIso
#print axioms geometricFieldEquiv
#print axioms geometric_genus_five
#print axioms geometricallyConnected
#print axioms geometric_globalDifferentials_five
end
end FourCorner.HpLiteralGeometric
