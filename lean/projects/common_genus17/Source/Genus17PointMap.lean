import Genus17Cover
import Genus17FieldGenus

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory IntermediateField
open NormalizedModelPointRestriction
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

def coverClosed (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (x : closedPoints (curve t κ h0 h1 hm)) : closedPoints (CommonSchemeModel.model t h0 h1 hm).C := by
  haveI := cover_isFinite t κ h0 h1 hm
  refine ⟨cover t κ h0 h1 hm x.1,?_⟩
  change IsClosed {cover t κ h0 h1 hm x.1}
  simpa only [Set.image_singleton] using (cover t κ h0 h1 hm).isClosedMap {x.1} x.2

/-- The actual finite cover maps every closed point, including poles and
boundary points, to the restriction of that same chosen function-field place. -/
theorem cover_point_restrict (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (x : closedPoints (curve t κ h0 h1 hm)) :
    ((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t) =
      (CommonSchemeModel.model t h0 h1 hm).placeOfPoint (coverClosed t κ h0 h1 hm x) := by
  letI : FiniteDimensional (RatFunc K) (baseField t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen K h0 h1 hm]; norm_num)
  letI := finite_over_line t κ h0 h1 hm
  letI : Fact (CommonLiteralField.ell K t ≠ 0) := ⟨CommonLiteralField.ell_ne_zero K t⟩
  obtain ⟨hf,hi⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator K (L := baseField t)
  obtain ⟨ef,ei⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator K (L := field t κ)
  letI := hf
  letI := hi
  letI := ef
  letI := ei
  letI : FiniteDimensional K⟮CommonLiteralField.ell K t⟯ (baseField t) := hf
  letI : FiniteDimensional K⟮(CommonLiteralField.ell K t)⁻¹⟯ (baseField t) := hi
  letI : FiniteDimensional K⟮NormalizationPointRestriction.inclusion (K := K) (E := field t κ) (CommonLiteralField.ell K t)⟯ (field t κ) := ef
  letI : FiniteDimensional K⟮(NormalizationPointRestriction.inclusion (K := K) (E := field t κ) (CommonLiteralField.ell K t))⁻¹⟯ (field t κ) := ei
  change ((NormalizedModelPointRestriction.sourceModel K (field t κ)).placeOfPoint x).restrict (baseField t) =
    (NormalizedModelPointRestriction.sourceModel K (baseField t)).placeOfPoint (coverClosed t κ h0 h1 hm x)
  rw [NormalizedModelPointRestriction.source_place K (field t κ)]
  have hb := NormalizedModelPointRestriction.source_place K (baseField t) (coverClosed t κ h0 h1 hm x)
  rw [hb]
  have h := NormalizationPointRestriction.point_restrict (CommonLiteralField.ell K t)
    (CurveModel.transcendental_towerGenerator K)
    (isoClosed (NormalizedModelCover.sourceIso K (field t κ)) x)
  refine h.trans (congrArg (CurveModel.gluedPlaceOfPoint K (CommonLiteralField.ell K t)
    (CurveModel.transcendental_towerGenerator K)) ?_)
  apply Subtype.ext
  have he : cover t κ h0 h1 hm ≫ (NormalizedModelCover.sourceIso K (baseField t)).hom =
      (NormalizedModelCover.sourceIso K (field t κ)).hom ≫
        NormalizationCoverMap.cover (fieldInclusion t κ) (CommonLiteralField.ell K t) := by
    set_option backward.isDefEq.respectTransparency false in
      simp only [cover,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact (congrArg (fun f => f x.1) he).symm

/-- Unramifiedness is the actual index of the source point's DVR place in
the native finite cover, on all closed points without an affine exception. -/
theorem cover_all_closed_indices_one (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (hκ : κ ≠ 0) (x : closedPoints (curve t κ h0 h1 hm)) :
    ((model t κ h0 h1 hm).placeOfPoint x).ramificationIndex (baseField t) = 1 :=
  all_places_unramified t κ h1 hm hκ _
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.cover_point_restrict
#print axioms FourCorner.Genus17Geometry.cover_all_closed_indices_one
