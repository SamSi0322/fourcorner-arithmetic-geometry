import HpConstantFieldComparison
import geometry.SchemeModelGeometricIntegral
import Slot03HighPullbackField
import ModelGenusBridge.KaehlerSheafGenus
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! The genuine canonical smooth proper completion of the exact Hasse
four-root field, with actual categorical constant-base-change and actual
global relative Kähler dimension five. No numerical genus is defined by fiat. -/
namespace FourCorner.HpSchemeModel

open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section

abbrev field (p : ℚ) := HpLiteralField.field ℚ p
abbrev modelFieldAlgebra (p : ℚ) : Algebra ℚ (field p) := HpFieldGeometry.constantAlgebra ℚ p
local instance constantAlgebra (p : ℚ) : Algebra ℚ (field p) := modelFieldAlgebra p
local instance constantModule (p : ℚ) : Module ℚ (field p) := Algebra.toModule

def model (p : ℚ) : CurveModel ℚ (field p) := by
  letI := HpLiteralField.finite_over_line ℚ p
  exact SchemeModelFiniteExtension.model ℚ (field p)

abbrev curve (p : ℚ) := (model p).C
abbrev toBase (p : ℚ) := (model p).toBase

theorem model_integral (p : ℚ) : IsIntegral (curve p) := inferInstance
theorem model_proper (p : ℚ) : IsProper (toBase p) := inferInstance
theorem model_smooth (p : ℚ) : SmoothOfRelativeDimension 1 (toBase p) := inferInstance

abbrev modelCover (p : ℚ) : (curve p).TwoAffineOpenCover := by
  letI := HpLiteralField.finite_over_line ℚ p
  exact SchemeModelFiniteExtension.twoAffineOpenCover ℚ (field p)

theorem cover0Nonempty (p : ℚ) : Nonempty (modelCover p).U0 := by
  letI := HpLiteralField.finite_over_line ℚ p
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U0 ℚ (field p)
theorem cover1Nonempty (p : ℚ) : Nonempty (modelCover p).U1 := by
  letI := HpLiteralField.finite_over_line ℚ p
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U1 ℚ (field p)
theorem cover01Nonempty (p : ℚ) : Nonempty ((modelCover p).U0 ⊓ (modelCover p).U1 : (curve p).Opens) := by
  letI := HpLiteralField.finite_over_line ℚ p
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_overlap ℚ (field p)

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem tensorDomainForAlgebra (L : Type) [Field L] [Algebra ℚ L] (p : ℚ) (hp : 1<p)
    (a : Algebra ℚ (field p)) :
    letI := a
    letI : Module ℚ (field p) := Algebra.toModule
    IsDomain (L ⊗[ℚ] field p) := by
  have he : a=modelFieldAlgebra p := Subsingleton.elim _ _
  subst a
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact HpTensorComparison.all_constants_domain ℚ L p (by linarith) (by linarith) (by linarith)

def fractionFieldEquivForAlgebra (L : Type) [Field L] [CharZero L] [Algebra ℚ L] (p : ℚ) (hp : 1<p)
    (a : Algebra ℚ (field p)) :
    letI := a
    letI : Module ℚ (field p) := Algebra.toModule
    letI := tensorDomainForAlgebra L p hp a
    FractionRing (L ⊗[ℚ] field p) ≃ₐ[L] HpLiteralField.field L (algebraMap ℚ L p) := by
  have he : a=modelFieldAlgebra p := Subsingleton.elim _ _
  subst a
  exact HpConstantFieldComparison.fractionFieldEquiv ℚ L p (by linarith) (by linarith) (by linarith)

theorem model_geometricallyIntegral (p : ℚ) (hp : 1<p) : GeometricallyIntegral (toBase p) := by
  letI := HpLiteralField.finite_over_line ℚ p
  apply SchemeModelGeometricIntegral.model_geometricallyIntegral ℚ (field p)
  intro L hL hA
  exact tensorDomainForAlgebra L p hp (modelFieldAlgebra p)

theorem model_geometricallyConnected (p : ℚ) (hp : 1<p) : GeometricallyConnected (toBase p) := by
  have h := model_geometricallyIntegral p hp
  refine ⟨fun {L} _ y {Z} fst snd hpb => ?_⟩
  have := h.geometrically_isIntegral y fst snd hpb
  infer_instance

abbrev geometricScheme (p : ℚ) := pullback (toBase p) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))
abbrev geometricToBase (p : ℚ) := pullback.snd (toBase p) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))

theorem geometricIntegral (p : ℚ) (hp : 1<p) : IsIntegral (geometricScheme p) := by
  letI := modelFieldAlgebra p
  letI : Module ℚ (field p) := Algebra.toModule
  haveI := tensorDomainForAlgebra (AlgebraicClosure ℚ) p hp (modelFieldAlgebra p)
  haveI := cover0Nonempty p
  haveI := cover1Nonempty p
  haveI := cover01Nonempty p
  exact SchemeModelGeometricIntegral.isIntegral_pullback (model p) (modelCover p) (AlgebraicClosure ℚ)

/-- Actual function field of the actual Qbar base change of this same
rational model, not a newly rebuilt object merely assigned a genus. -/
def geometricFieldEquiv (p : ℚ) (hp : 1<p) :
    letI := geometricIntegral p hp
    letI := (baseToFunctionField (geometricToBase p)).toAlgebra
    HpLiteralField.field (AlgebraicClosure ℚ) (algebraMap ℚ (AlgebraicClosure ℚ) p) ≃ₐ[AlgebraicClosure ℚ]
      (geometricScheme p).functionField := by
  letI := geometricIntegral p hp
  letI := (baseToFunctionField (geometricToBase p)).toAlgebra
  letI := modelFieldAlgebra p
  letI : Module ℚ (field p) := Algebra.toModule
  haveI := tensorDomainForAlgebra (AlgebraicClosure ℚ) p hp (modelFieldAlgebra p)
  haveI := cover0Nonempty p
  haveI := cover1Nonempty p
  haveI := cover01Nonempty p
  exact (fractionFieldEquivForAlgebra (AlgebraicClosure ℚ) p hp (modelFieldAlgebra p)).symm.trans
    (Slot03High.pullbackFunctionFieldEquiv (model p) (modelCover p) (AlgebraicClosure ℚ))

theorem geometric_genus_five (p : ℚ) (hp : 1<p) :
    letI := geometricIntegral p hp
    letI := (baseToFunctionField (geometricToBase p)).toAlgebra
    genusFF (AlgebraicClosure ℚ) (geometricScheme p).functionField=5 := by
  letI := geometricIntegral p hp
  letI := (baseToFunctionField (geometricToBase p)).toAlgebra
  exact (genusFF_eq_of_algEquiv (geometricFieldEquiv p hp)).symm.trans
    (HpGeometricGenus.rational_geometric_genus_five p hp)

theorem geometricProper (p : ℚ) : IsProper (geometricToBase p) := by
  haveI := model_proper p
  unfold geometricToBase
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem geometricSmooth (p : ℚ) : SmoothOfRelativeDimension 1 (geometricToBase p) := by
  haveI := model_smooth p
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P:=@SmoothOfRelativeDimension 1) _ _ inferInstance

/-- Intrinsic genus five as the dimension of actual global relative Kähler
differentials on the actual geometric base change of this Q-curve. -/
theorem geometric_globalDifferentials_five (p : ℚ) (hp : 1<p) :
    let c := geometricToBase p
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤)=5 := by
  let c := geometricToBase p
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
  letI := geometricIntegral p hp
  letI := geometricProper p
  letI := geometricSmooth p
  let V := (modelCover p).pullback (toBase p) (AlgebraicClosure ℚ)
  obtain ⟨hfin,hrank⟩ := KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF V c
  exact ⟨hfin,hrank.trans (geometric_genus_five p hp)⟩

#print axioms model
#print axioms model_geometricallyIntegral
#print axioms geometricFieldEquiv
#print axioms geometric_globalDifferentials_five

end
end FourCorner.HpSchemeModel
