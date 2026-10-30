import NormalizationCoefficientMap
import GenericNormalizedGluing

noncomputable section
namespace FourCorner.NormalizationCoverMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open FourCorner.NormalizationCoefficientMap
universe u
variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (φ : F →ₐ[K] E) (s : F) [Fact (s ≠ 0)]
local instance mapped_nonzero : Fact (φ s ≠ 0) := ⟨fun h => (Fact.out : s ≠ 0) (φ.injective (h.trans (map_zero φ).symm))⟩

def zeroSchemeMap : CurveModel.X₀ K (φ s) ⟶ CurveModel.X₀ K s :=
  Spec.map (CommRingCat.ofHom (zeroMap φ s))
def infinitySchemeMap : CurveModel.XInf K (φ s) ⟶ CurveModel.XInf K s :=
  Spec.map (CommRingCat.ofHom (infinityMap φ s))
def overlapSchemeMap : CurveModel.XOverlap K (φ s) ⟶ CurveModel.XOverlap K s :=
  Spec.map (CommRingCat.ofHom (overlapMap φ s))

lemma zero_scheme_square : CurveModel.f₀ K (φ s) ≫ zeroSchemeMap φ s =
    overlapSchemeMap φ s ≫ CurveModel.f₀ K s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact zero_overlap_compatible φ s
lemma infinity_scheme_square : CurveModel.fInf K (φ s) ≫ infinitySchemeMap φ s =
    overlapSchemeMap φ s ≫ CurveModel.fInf K s := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact infinity_overlap_compatible φ s

/-- The actual function-field morphism on the glued normalization schemes.
Its construction glues the integral-closure maps, with proved overlap compatibility. -/
def cover : CurveModel.glued K (φ s) ⟶ CurveModel.glued K s :=
  GenericNormalizedGluing.desc K E (φ s) (zeroSchemeMap φ s ≫ CurveModel.ι₀ K s)
    (infinitySchemeMap φ s ≫ CurveModel.ιInf K s) (by
      rw [← Category.assoc, zero_scheme_square, Category.assoc, CurveModel.glue_condition,
        ← Category.assoc, ← infinity_scheme_square, Category.assoc])

@[reassoc] theorem zero_cover : CurveModel.ι₀ K (φ s) ≫ cover φ s =
    zeroSchemeMap φ s ≫ CurveModel.ι₀ K s := GenericNormalizedGluing.zero_desc K E (φ s) _ _ _
@[reassoc] theorem infinity_cover : CurveModel.ιInf K (φ s) ≫ cover φ s =
    infinitySchemeMap φ s ≫ CurveModel.ιInf K s := GenericNormalizedGluing.infinity_desc K E (φ s) _ _ _

/-- The glued normalization cover lies over the original coefficient field. -/
theorem cover_over : cover φ s ≫ CurveModel.gluedToBase K s = CurveModel.gluedToBase K (φ s) := by
  apply GenericNormalizedGluing.hom_ext K E (φ s)
  · rw [← Category.assoc,zero_cover,Category.assoc,CurveModel.ι₀_gluedToBase,CurveModel.ι₀_gluedToBase]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change zeroMap φ s (algebraMap K _ a) = algebraMap K _ a
    exact chartMap_constants φ _ _ _ a
  · rw [← Category.assoc,infinity_cover,Category.assoc,CurveModel.ιInf_gluedToBase,CurveModel.ιInf_gluedToBase]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change infinityMap φ s (algebraMap K _ a) = algebraMap K _ a
    exact chartMap_constants φ _ _ _ a

#print axioms cover
#print axioms zero_cover
#print axioms infinity_cover
#print axioms cover_over
end FourCorner.NormalizationCoverMap
