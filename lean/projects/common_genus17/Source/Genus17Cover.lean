import Genus17Model

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory IntermediateField
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

/-- The native finite normalization morphism to the very same accepted D_t. -/
def cover (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    curve t κ h0 h1 hm ⟶ (CommonSchemeModel.model t h0 h1 hm).C := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  letI := finite_over_line t κ h0 h1 hm
  letI : Fact (CommonLiteralField.ell K t ≠ 0) := ⟨CommonLiteralField.ell_ne_zero K t⟩
  exact (NormalizedModelCover.sourceIso K (field t κ)).hom ≫
    NormalizationCoverMap.cover (fieldInclusion t κ) (CommonLiteralField.ell K t) ≫
      (NormalizedModelCover.sourceIso K (baseField t)).inv

theorem cover_isFinite (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    IsFinite (cover t κ h0 h1 hm) := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  letI := finite_over_line t κ h0 h1 hm
  letI : Fact (CommonLiteralField.ell K t ≠ 0) := ⟨CommonLiteralField.ell_ne_zero K t⟩
  obtain ⟨hf,hi⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator K (L := field t κ)
  letI : FiniteDimensional K⟮fieldInclusion t κ (CommonLiteralField.ell K t)⟯ (field t κ) := hf
  letI : FiniteDimensional K⟮(fieldInclusion t κ (CommonLiteralField.ell K t))⁻¹⟯ (field t κ) := hi
  haveI := FiniteNormalizationCover.cover_isFinite (fieldInclusion t κ) (CommonLiteralField.ell K t)
  unfold cover
  exact MorphismProperty.comp_mem @IsFinite _ _
    (MorphismProperty.of_isIso @IsFinite (NormalizedModelCover.sourceIso K (field t κ)).hom)
    (MorphismProperty.comp_mem @IsFinite _ _
      (FiniteNormalizationCover.cover_isFinite (fieldInclusion t κ) (CommonLiteralField.ell K t))
      (MorphismProperty.of_isIso @IsFinite (NormalizedModelCover.sourceIso K (baseField t)).inv))

/-- The cover sends the original zero normalization chart by the literal
integral-closure coefficient homomorphism. -/
theorem cover_zero_chart (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI : FiniteDimensional (RatFunc K) (field t κ) := finite_over_line t κ h0 h1 hm
    letI : FiniteDimensional (RatFunc K) (baseField t) :=
      FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
    letI : Fact (CommonLiteralField.ell K t ≠ 0) := ⟨CommonLiteralField.ell_ne_zero K t⟩
    letI : Fact (ell t κ ≠ 0) := ⟨(map_ne_zero (fieldInclusion t κ)).mpr (CommonLiteralField.ell_ne_zero K t)⟩
    (CurveModel.ι₀ K (ell t κ) ≫ (NormalizedModelCover.sourceIso K (field t κ)).inv) ≫ cover t κ h0 h1 hm =
      NormalizationCoverMap.zeroSchemeMap (fieldInclusion t κ) (CommonLiteralField.ell K t) ≫
        (CurveModel.ι₀ K (CommonLiteralField.ell K t) ≫ (NormalizedModelCover.sourceIso K (baseField t)).inv) := by
  set_option backward.isDefEq.respectTransparency false in
    simp only [ell,cover,Category.assoc,Iso.inv_hom_id_assoc,NormalizationCoverMap.zero_cover_assoc]
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.cover
#print axioms FourCorner.Genus17Geometry.cover_isFinite
#print axioms FourCorner.Genus17Geometry.cover_zero_chart
