import Genus17ConstantFieldComparison
import Genus17GeometricModel
import Genus17FieldGenus
import Slot03HighPullbackField

noncomputable section
namespace FourCorner.Genus17GeometricGenus
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Genus17Geometry
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

lemma tensorDomainForAlgebra (L : Type) [Field L] [Algebra ℚ L] (t κ : ℚ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) (a : Algebra ℚ (field t κ)) :
    letI := a
    letI : Module ℚ (field t κ) := Algebra.toModule
    IsDomain (L ⊗[ℚ] field t κ) := by
  have ha : a = modelFieldAlgebra t κ := Subsingleton.elim _ _
  subst a
  exact Genus17GeometricField.all_constants_domain ℚ L h0 h1 hm hκ

def fractionFieldEquivForAlgebra (L : Type) [Field L] [CharZero L] [Algebra ℚ L] (t κ : ℚ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) (a : Algebra ℚ (field t κ)) :
    letI := a
    letI : Module ℚ (field t κ) := Algebra.toModule
    letI := tensorDomainForAlgebra L t κ h0 h1 hm hκ a
    FractionRing (L ⊗[ℚ] field t κ) ≃ₐ[L]
      field (algebraMap ℚ L t) (algebraMap ℚ L κ) := by
  have ha : a = modelFieldAlgebra t κ := Subsingleton.elim _ _
  subst a
  exact Genus17ConstantFieldComparison.fractionFieldEquiv ℚ L h0 h1 hm hκ

abbrev geometricScheme (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :=
  pullback (toBase t κ h0 h1 hm) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))
abbrev geometricToBase (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :=
  pullback.snd (toBase t κ h0 h1 hm) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))

lemma geometricIntegral (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    IsIntegral (geometricScheme t κ h0 h1 hm) := by
  letI := modelFieldAlgebra t κ
  letI : Module ℚ (field t κ) := Algebra.toModule
  haveI := tensorDomainForAlgebra (AlgebraicClosure ℚ) t κ h0 h1 hm hκ (modelFieldAlgebra t κ)
  haveI := cover0Nonempty t κ h0 h1 hm
  haveI := cover1Nonempty t κ h0 h1 hm
  haveI := cover01Nonempty t κ h0 h1 hm
  exact SchemeModelGeometricIntegral.isIntegral_pullback (model t κ h0 h1 hm) (modelCover t κ h0 h1 hm) (AlgebraicClosure ℚ)

/-- Function-field comparison on the actual Qbar pullback of this same rational
five-root model, obtained through its real two affine chart rings. -/
def geometricFieldEquiv (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := geometricIntegral t κ h0 h1 hm hκ
    letI := (baseToFunctionField (geometricToBase t κ h0 h1 hm)).toAlgebra
    field (algebraMap ℚ (AlgebraicClosure ℚ) t) (algebraMap ℚ (AlgebraicClosure ℚ) κ) ≃ₐ[AlgebraicClosure ℚ]
      (geometricScheme t κ h0 h1 hm).functionField := by
  letI := geometricIntegral t κ h0 h1 hm hκ
  letI := (baseToFunctionField (geometricToBase t κ h0 h1 hm)).toAlgebra
  letI := modelFieldAlgebra t κ
  letI : Module ℚ (field t κ) := Algebra.toModule
  haveI := tensorDomainForAlgebra (AlgebraicClosure ℚ) t κ h0 h1 hm hκ (modelFieldAlgebra t κ)
  haveI := cover0Nonempty t κ h0 h1 hm
  haveI := cover1Nonempty t κ h0 h1 hm
  haveI := cover01Nonempty t κ h0 h1 hm
  exact (fractionFieldEquivForAlgebra (AlgebraicClosure ℚ) t κ h0 h1 hm hκ (modelFieldAlgebra t κ)).symm.trans
    (Slot03High.pullbackFunctionFieldEquiv (model t κ h0 h1 hm) (modelCover t κ h0 h1 hm) (AlgebraicClosure ℚ))

lemma geometric_genus_seventeen (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := geometricIntegral t κ h0 h1 hm hκ
    letI := (baseToFunctionField (geometricToBase t κ h0 h1 hm)).toAlgebra
    genusFF (AlgebraicClosure ℚ) (geometricScheme t κ h0 h1 hm).functionField = 17 := by
  letI := geometricIntegral t κ h0 h1 hm hκ
  letI := (baseToFunctionField (geometricToBase t κ h0 h1 hm)).toAlgebra
  have h0' : algebraMap ℚ (AlgebraicClosure ℚ) t ≠ 0 := (map_ne_zero _).mpr h0
  have h1' : algebraMap ℚ (AlgebraicClosure ℚ) t ≠ 1 := by simpa only [map_one] using (algebraMap ℚ (AlgebraicClosure ℚ)).injective.ne h1
  have hm' : algebraMap ℚ (AlgebraicClosure ℚ) t ≠ -1 := by simpa only [map_neg,map_one] using (algebraMap ℚ (AlgebraicClosure ℚ)).injective.ne hm
  have hκ' : algebraMap ℚ (AlgebraicClosure ℚ) κ ≠ 0 := (map_ne_zero _).mpr hκ
  exact (genusFF_eq_of_algEquiv (geometricFieldEquiv t κ h0 h1 hm hκ)).symm.trans
    (genusFF_seventeen _ _ h0' h1' hm' hκ')

lemma geometricProper (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    IsProper (geometricToBase t κ h0 h1 hm) := by
  haveI := model_proper t κ h0 h1 hm
  unfold geometricToBase
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma geometricSmooth (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    SmoothOfRelativeDimension 1 (geometricToBase t κ h0 h1 hm) := by
  haveI := model_smooth t κ h0 h1 hm
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

/-- The genus is seventeen as the dimension of actual global relative Kahler
differentials on the actual categorical Qbar pullback of this same Q curve. -/
theorem geometric_globalDifferentials_seventeen (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    let c := geometricToBase t κ h0 h1 hm
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) = 17 := by
  let c := geometricToBase t κ h0 h1 hm
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
  letI := geometricIntegral t κ h0 h1 hm hκ
  letI := geometricProper t κ h0 h1 hm
  letI := geometricSmooth t κ h0 h1 hm
  let V := (modelCover t κ h0 h1 hm).pullback (toBase t κ h0 h1 hm) (AlgebraicClosure ℚ)
  obtain ⟨hfin,hrk⟩ := KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF V c
  exact ⟨hfin,hrk.trans (geometric_genus_seventeen t κ h0 h1 hm hκ)⟩
end FourCorner.Genus17GeometricGenus
#print axioms FourCorner.Genus17GeometricGenus.geometricFieldEquiv
#print axioms FourCorner.Genus17GeometricGenus.geometric_globalDifferentials_seventeen
