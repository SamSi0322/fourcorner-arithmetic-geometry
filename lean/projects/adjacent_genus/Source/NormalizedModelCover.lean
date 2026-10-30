import NormalizationCoverField
import AdjacentPostNormalizedCharts

noncomputable section
namespace FourCorner.NormalizedModelCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IntermediateField
open FourCorner.AdjacentPostNormalizedCharts
universe u
variable (K E : Type u) [Field K] [CharZero K] [Field E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev sourceModel := SchemeModelFiniteExtension.model K E
abbrev baseModel := SchemeModelFiniteExtension.model K (RatFunc K)
abbrev fieldInclusion : RatFunc K →ₐ[K] E := IsScalarTower.toAlgHom K (RatFunc K) E

local instance parameter_nonzero : Fact (RatFunc.X ≠ (0 : RatFunc K)) := ⟨RatFunc.X_ne_zero⟩
local instance mapped_nonzero : Fact (fieldInclusion K E RatFunc.X ≠ 0) :=
  ⟨CurveModel.towerGenerator_ne_zero K⟩

def sourceIso : (sourceModel K E).C ≅ CurveModel.glued K (fieldInclusion K E RatFunc.X) :=
  eqToIso (generic_scheme_eq_normalized_gluing K E)

def baseIso : (baseModel K).C ≅ CurveModel.glued K (RatFunc.X : RatFunc K) :=
  eqToIso (by
    simpa only [CurveModel.towerGenerator,Algebra.algebraMap_self,RingHom.id_apply] using
      (generic_scheme_eq_normalized_gluing K (RatFunc K)))

/-- The canonical finite normalization cover for the specified actual rational-function-field extension. -/
def cover : (sourceModel K E).C ⟶ (baseModel K).C :=
  (sourceIso K E).hom ≫ NormalizationCoverMap.cover (fieldInclusion K E) RatFunc.X ≫ (baseIso K).inv

/-- This is a native finite morphism between the actual canonical Scheme models. -/
theorem cover_isFinite : IsFinite (cover K E) := by
  obtain ⟨h0,hInf⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)
  haveI : FiniteDimensional K⟮fieldInclusion K E RatFunc.X⟯ E := h0
  haveI : FiniteDimensional K⟮(fieldInclusion K E RatFunc.X)⁻¹⟯ E := hInf
  haveI := FiniteNormalizationCover.cover_isFinite (fieldInclusion K E) RatFunc.X
  unfold cover
  infer_instance

/-- The source normalization zero chart maps by the actual integral-closure ring map. -/
theorem zero_cover :
    (CurveModel.ι₀ K (fieldInclusion K E RatFunc.X) ≫ (sourceIso K E).inv) ≫ cover K E =
      NormalizationCoverMap.zeroSchemeMap (fieldInclusion K E) RatFunc.X ≫
        (CurveModel.ι₀ K (RatFunc.X : RatFunc K) ≫ (baseIso K).inv) := by
  simp only [cover,Category.assoc,Iso.inv_hom_id_assoc,NormalizationCoverMap.zero_cover_assoc]

theorem infinity_cover :
    (CurveModel.ιInf K (fieldInclusion K E RatFunc.X) ≫ (sourceIso K E).inv) ≫ cover K E =
      NormalizationCoverMap.infinitySchemeMap (fieldInclusion K E) RatFunc.X ≫
        (CurveModel.ιInf K (RatFunc.X : RatFunc K) ≫ (baseIso K).inv) := by
  simp only [cover,Category.assoc,Iso.inv_hom_id_assoc,NormalizationCoverMap.infinity_cover_assoc]

/-- The actual finite model cover induces precisely the original supplied field inclusion. -/
theorem generic_cover :
    (NormalizationCoverField.fieldPoint K E (fieldInclusion K E RatFunc.X) ≫ (sourceIso K E).inv) ≫ cover K E =
      Spec.map (CommRingCat.ofHom (fieldInclusion K E).toRingHom) ≫
        (NormalizationCoverField.fieldPoint K (RatFunc K) RatFunc.X ≫ (baseIso K).inv) := by
  simp only [cover,Category.assoc,Iso.inv_hom_id_assoc]
  rw [← Category.assoc,NormalizationCoverField.generic_cover,Category.assoc]

#print axioms cover
#print axioms cover_isFinite
#print axioms zero_cover
#print axioms infinity_cover
#print axioms generic_cover
end FourCorner.NormalizedModelCover
