import Genus17Cover
import CanonicalGenericField

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

def sourceFieldPoint (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Spec (.of (field t κ)) ⟶ curve t κ h0 h1 hm := by
  letI := finite_over_line t κ h0 h1 hm
  exact CanonicalGenericField.point K (field t κ)

def targetFieldPoint (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Spec (.of (baseField t)) ⟶ (CommonSchemeModel.model t h0 h1 hm).C := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact CanonicalGenericField.point K (baseField t)

/-- The native finite cover induces precisely the original five-root/four-root
field inclusion, retaining the literal ell and all four original ordered roots. -/
theorem cover_generic (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    sourceFieldPoint t κ h0 h1 hm ≫ cover t κ h0 h1 hm =
      Spec.map (CommRingCat.ofHom (fieldInclusion t κ).toRingHom) ≫ targetFieldPoint t h0 h1 hm := by
  letI := finite_over_line t κ h0 h1 hm
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  letI : Fact (CommonLiteralField.ell K t ≠ 0) := ⟨CommonLiteralField.ell_ne_zero K t⟩
  letI : Fact (fieldInclusion t κ (CommonLiteralField.ell K t) ≠ 0) :=
    ⟨(map_ne_zero (fieldInclusion t κ)).mpr (CommonLiteralField.ell_ne_zero K t)⟩
  change (NormalizationCoverField.fieldPoint K (field t κ)
      (fieldInclusion t κ (CommonLiteralField.ell K t)) ≫
        (NormalizedModelCover.sourceIso K (field t κ)).inv) ≫ cover t κ h0 h1 hm =
    Spec.map (CommRingCat.ofHom (fieldInclusion t κ).toRingHom) ≫
      (NormalizationCoverField.fieldPoint K (baseField t) (CommonLiteralField.ell K t) ≫
        (NormalizedModelCover.sourceIso K (baseField t)).inv)
  set_option backward.isDefEq.respectTransparency false in
    simp only [cover,Category.assoc,Iso.inv_hom_id_assoc]
  erw [← Category.assoc,NormalizationCoverField.generic_cover,Category.assoc]

def sourceFieldEquiv (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (curve t κ h0 h1 hm).functionField ≃+* field t κ := by
  letI := finite_over_line t κ h0 h1 hm
  exact CanonicalGenericField.equiv K (field t κ)
def targetFieldEquiv (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (CommonSchemeModel.model t h0 h1 hm).C.functionField ≃+* baseField t := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact CanonicalGenericField.equiv K (baseField t)

theorem source_field_factor (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Spec.map (CommRingCat.ofHom (sourceFieldEquiv t κ h0 h1 hm).toRingHom) ≫
      (curve t κ h0 h1 hm).fromSpecStalk (genericPoint (curve t κ h0 h1 hm)) = sourceFieldPoint t κ h0 h1 hm := by
  letI := finite_over_line t κ h0 h1 hm
  exact CanonicalGenericField.factor K (field t κ)
theorem target_field_factor (t : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Spec.map (CommRingCat.ofHom (targetFieldEquiv t h0 h1 hm).toRingHom) ≫
      (CommonSchemeModel.model t h0 h1 hm).C.fromSpecStalk (genericPoint (CommonSchemeModel.model t h0 h1 hm).C) = targetFieldPoint t h0 h1 hm := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  exact CanonicalGenericField.factor K (baseField t)

def coverFieldPullback (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (CommonSchemeModel.model t h0 h1 hm).C.functionField →+* (curve t κ h0 h1 hm).functionField :=
  (sourceFieldEquiv t κ h0 h1 hm).symm.toRingHom.comp
    ((fieldInclusion t κ).toRingHom.comp (targetFieldEquiv t h0 h1 hm).toRingHom)

theorem cover_generic_stalk_square (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (curve t κ h0 h1 hm).fromSpecStalk (genericPoint (curve t κ h0 h1 hm)) ≫ cover t κ h0 h1 hm =
      Spec.map (CommRingCat.ofHom (coverFieldPullback t κ h0 h1 hm)) ≫
        (CommonSchemeModel.model t h0 h1 hm).C.fromSpecStalk (genericPoint (CommonSchemeModel.model t h0 h1 hm).C) := by
  let e := sourceFieldEquiv t κ h0 h1 hm
  have hs : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ sourceFieldPoint t κ h0 h1 hm =
      (curve t κ h0 h1 hm).fromSpecStalk (genericPoint (curve t κ h0 h1 hm)) := by
    rw [← source_field_factor,← Category.assoc,← Spec.map_comp]
    have he : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact e.symm_apply_apply a
    rw [he]
    simp
  rw [← hs,Category.assoc,cover_generic,← target_field_factor]
  rw [← Category.assoc,← Category.assoc,← Spec.map_comp,← Spec.map_comp]
  rfl

/-- Actual degree two on the generic stalk fields of the same native cover. -/
theorem cover_degree_two (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
    Module.finrank (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField = 2 := by
  letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
  have h := Algebra.finrank_eq_of_equiv_equiv (targetFieldEquiv t h0 h1 hm).symm
    (sourceFieldEquiv t κ h0 h1 hm).symm (by
      apply RingHom.ext
      intro a
      change (sourceFieldEquiv t κ h0 h1 hm).symm
        (fieldInclusion t κ ((targetFieldEquiv t h0 h1 hm) ((targetFieldEquiv t h0 h1 hm).symm a))) =
          (sourceFieldEquiv t κ h0 h1 hm).symm (fieldInclusion t κ a)
      rw [RingEquiv.apply_symm_apply])
  exact h.symm.trans (degree_two t κ h0 h1 hm hκ)
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.cover_generic
#print axioms FourCorner.Genus17Geometry.source_field_factor
#print axioms FourCorner.Genus17Geometry.target_field_factor
#print axioms FourCorner.Genus17Geometry.cover_generic_stalk_square
#print axioms FourCorner.Genus17Geometry.cover_degree_two
