import FiniteNormalizationCover

noncomputable section
namespace FourCorner.NormalizationCoverField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open FourCorner.NormalizationCoefficientMap FourCorner.NormalizationCoverMap
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual function-field point of the zero normalization chart. -/
def fieldPoint (K L : Type u) [Field K] [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)] :
    Spec (.of L) ⟶ CurveModel.glued K t :=
  Spec.map (CommRingCat.ofHom (algebraMap (CurveModel.chartRing K ({t} : Set L)) L)) ≫ CurveModel.ι₀ K t

variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]

lemma field_square_value (φ : F →ₐ[K] E) (s : F) (a : CurveModel.chartRing K ({s} : Set F)) :
    algebraMap (CurveModel.chartRing K ({φ s} : Set E)) E (zeroMap φ s a) =
      φ (algebraMap (CurveModel.chartRing K ({s} : Set F)) F a) := zeroMap_coe φ s a

lemma field_square (φ : F →ₐ[K] E) (s : F) :
    (algebraMap (CurveModel.chartRing K ({φ s} : Set E)) E).comp (zeroMap φ s) =
      φ.toRingHom.comp (algebraMap (CurveModel.chartRing K ({s} : Set F)) F) :=
  RingHom.ext (field_square_value φ s)

variable (φ : F →ₐ[K] E) (s : F) [Fact (s ≠ 0)]
local instance mapped_nonzero : Fact (φ s ≠ 0) :=
  ⟨fun h => (Fact.out : s ≠ 0) (φ.injective (h.trans (map_zero φ).symm))⟩

/-- The constructed finite normalization cover has exactly the supplied original
function-field embedding, expressed by a commuting diagram of genuine Scheme morphisms. -/
theorem generic_cover : fieldPoint K E (φ s) ≫ cover φ s =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ fieldPoint K F s := by
  unfold fieldPoint
  rw [Category.assoc,zero_cover]
  change Spec.map _ ≫ (Spec.map _ ≫ CurveModel.ι₀ K s) =
    Spec.map _ ≫ (Spec.map _ ≫ CurveModel.ι₀ K s)
  rw [← Category.assoc,← Category.assoc,← Spec.map_comp,← Spec.map_comp]
  apply congrArg (fun g => g ≫ CurveModel.ι₀ K s)
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact field_square φ s

#print axioms field_square
#print axioms generic_cover
end FourCorner.NormalizationCoverField
