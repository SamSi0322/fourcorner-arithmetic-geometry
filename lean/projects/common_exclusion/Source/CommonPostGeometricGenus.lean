import CommonSchemeGeometricIntegral
import CommonSchemeDifferentials
import CommonConstantFieldComparison
import Slot03HighPullbackField

noncomputable section
namespace FourCorner.CommonPostGeometricGenus
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open CommonSchemeModel
universe u

abbrev modelFieldAlgebra {K : Type u} [Field K] [CharZero K] (t : K) :
    Algebra K (CommonLiteralField.field K t) := inferInstance

abbrev modelCover {K : Type u} [Field K] [CharZero K] (t : K)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : (model t h0 h1 hm).C.TwoAffineOpenCover := by
  letI : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact SchemeModelFiniteExtension.twoAffineOpenCover K (CommonLiteralField.field K t)

lemma cover0Nonempty {K : Type u} [Field K] [CharZero K] (t : K)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : Nonempty (modelCover t h0 h1 hm).U0 := by
  letI : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U0 K (CommonLiteralField.field K t)
lemma cover1Nonempty {K : Type u} [Field K] [CharZero K] (t : K)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) : Nonempty (modelCover t h0 h1 hm).U1 := by
  letI : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U1 K (CommonLiteralField.field K t)
lemma cover01Nonempty {K : Type u} [Field K] [CharZero K] (t : K)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Nonempty ((modelCover t h0 h1 hm).U0 ⊓ (modelCover t h0 h1 hm).U1 : (model t h0 h1 hm).C.Opens) := by
  letI : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_overlap K (CommonLiteralField.field K t)

lemma tensorDomainForAlgebra (L : Type) [Field L] [Algebra ℚ L] (t : ℚ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (a : Algebra ℚ (CommonLiteralField.field ℚ t)) :
    letI := a
    IsDomain (L ⊗[ℚ] CommonLiteralField.field ℚ t) := by
  have ha : a = modelFieldAlgebra t := Subsingleton.elim _ _
  subst a
  exact CommonGeometricField.all_constants_domain ℚ L h0 h1 hm

def fractionFieldEquivForAlgebra (L : Type) [Field L] [CharZero L] [Algebra ℚ L] (t : ℚ)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (a : Algebra ℚ (CommonLiteralField.field ℚ t)) :
    letI := a
    letI := tensorDomainForAlgebra L t h0 h1 hm a
    FractionRing (L ⊗[ℚ] CommonLiteralField.field ℚ t) ≃ₐ[L]
      CommonLiteralField.field L (algebraMap ℚ L t) := by
  have ha : a = modelFieldAlgebra t := Subsingleton.elim _ _
  subst a
  exact CommonConstantFieldComparison.fractionFieldEquiv ℚ L h0 h1 hm

abbrev geometricScheme (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :=
  pullback (modelToBase t h0 h1 hm) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))
abbrev geometricToBase (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :=
  pullback.snd (modelToBase t h0 h1 hm) (Scheme.TwoAffineOpenCover.specMap ℚ (AlgebraicClosure ℚ))

lemma geometricIntegral (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    IsIntegral (geometricScheme t h0 h1 hm) := by
  letI := modelFieldAlgebra t
  haveI := tensorDomainForAlgebra (AlgebraicClosure ℚ) t h0 h1 hm (modelFieldAlgebra t)
  haveI := cover0Nonempty t h0 h1 hm
  haveI := cover1Nonempty t h0 h1 hm
  haveI := cover01Nonempty t h0 h1 hm
  exact SchemeModelGeometricIntegral.isIntegral_pullback (model t h0 h1 hm) (modelCover t h0 h1 hm) (AlgebraicClosure ℚ)

def geometricFieldEquiv (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := geometricIntegral t h0 h1 hm
    letI := (baseToFunctionField (geometricToBase t h0 h1 hm)).toAlgebra
    CommonLiteralField.field (AlgebraicClosure ℚ) (algebraMap ℚ (AlgebraicClosure ℚ) t) ≃ₐ[AlgebraicClosure ℚ]
      (geometricScheme t h0 h1 hm).functionField := by
  letI := geometricIntegral t h0 h1 hm
  letI := (baseToFunctionField (geometricToBase t h0 h1 hm)).toAlgebra
  letI := modelFieldAlgebra t
  haveI := tensorDomainForAlgebra (AlgebraicClosure ℚ) t h0 h1 hm (modelFieldAlgebra t)
  haveI := cover0Nonempty t h0 h1 hm
  haveI := cover1Nonempty t h0 h1 hm
  haveI := cover01Nonempty t h0 h1 hm
  exact (fractionFieldEquivForAlgebra (AlgebraicClosure ℚ) t h0 h1 hm (modelFieldAlgebra t)).symm.trans
    (Slot03High.pullbackFunctionFieldEquiv (model t h0 h1 hm) (modelCover t h0 h1 hm) (AlgebraicClosure ℚ))

/-- Genus nine on the actual categorical Qbar pullback of the original rational D_t model. -/
theorem geometric_genus_nine (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := geometricIntegral t h0 h1 hm
    letI := (baseToFunctionField (geometricToBase t h0 h1 hm)).toAlgebra
    genusFF (AlgebraicClosure ℚ) (geometricScheme t h0 h1 hm).functionField = 9 := by
  letI := geometricIntegral t h0 h1 hm
  letI := (baseToFunctionField (geometricToBase t h0 h1 hm)).toAlgebra
  exact (genusFF_eq_of_algEquiv (geometricFieldEquiv t h0 h1 hm)).symm.trans
    (CommonLiteralField.genusFF_eq_nine
      ((map_ne_zero (algebraMap ℚ (AlgebraicClosure ℚ))).mpr h0)
      (by intro h; apply h1; exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective (h.trans (map_one _).symm))
      (by intro h; apply hm; exact (algebraMap ℚ (AlgebraicClosure ℚ)).injective (h.trans (map_neg _ 1 |>.trans (congrArg Neg.neg (map_one _))).symm)))


lemma geometricProper (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    IsProper (geometricToBase t h0 h1 hm) := by
  haveI := model_proper t h0 h1 hm
  unfold geometricToBase modelToBase
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma geometricSmooth (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    SmoothOfRelativeDimension 1 (geometricToBase t h0 h1 hm) := by
  haveI := model_smooth t h0 h1 hm
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

/-- The actual geometric genus of the same rational D_t model is nine, computed
as the dimension of global Kahler differentials on its categorical Qbar pullback. -/
theorem geometric_globalDifferentials_nine (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    let c := geometricToBase t h0 h1 hm
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
      Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) = 9 := by
  let c := geometricToBase t h0 h1 hm
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
  letI := geometricIntegral t h0 h1 hm
  letI := geometricProper t h0 h1 hm
  letI := geometricSmooth t h0 h1 hm
  let V := (modelCover t h0 h1 hm).pullback (modelToBase t h0 h1 hm) (AlgebraicClosure ℚ)
  obtain ⟨hfin,hrk⟩ := KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF V c
  exact ⟨hfin,hrk.trans (geometric_genus_nine t h0 h1 hm)⟩

end FourCorner.CommonPostGeometricGenus
#print axioms FourCorner.CommonPostGeometricGenus.geometricFieldEquiv
#print axioms FourCorner.CommonPostGeometricGenus.geometric_genus_nine

#print axioms FourCorner.CommonPostGeometricGenus.geometric_globalDifferentials_nine
