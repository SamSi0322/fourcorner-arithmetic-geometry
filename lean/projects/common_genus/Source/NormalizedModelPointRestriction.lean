import NormalizationPointRestriction
import NormalizedModelCover

noncomputable section
namespace FourCorner.NormalizedModelPointRestriction
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
universe u
variable (K E : Type u) [Field K] [CharZero K] [Field E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev sourceModel := NormalizedModelCover.sourceModel K E
abbrev baseModel := NormalizedModelCover.baseModel K

def isoClosed {X Y : Scheme.{u}} (e : X ≅ Y) (x : closedPoints X) : closedPoints Y :=
  ⟨e.hom x.1, by change IsClosed {e.hom x.1}; simpa only [Set.image_singleton] using e.hom.isClosedMap {x.1} x.2⟩

local instance parameterNonzero : Fact (CurveModel.towerGenerator K (L := E) ≠ 0) :=
  ⟨CurveModel.towerGenerator_ne_zero K⟩

local instance sourceZeroFinite : FiniteDimensional K⟮CurveModel.towerGenerator K (L := E)⟯ E :=
  (CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)).1
local instance sourceInfinityFinite : FiniteDimensional K⟮(CurveModel.towerGenerator K (L := E))⁻¹⟯ E :=
  (CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)).2

private theorem model_eq : SchemeModelFiniteExtension.model K E =
    CurveModel.ofGenerator K (CurveModel.towerGenerator K (L := E))
      (CurveModel.transcendental_towerGenerator K) := by
  unfold SchemeModelFiniteExtension.model
  obtain ⟨hf,hi⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)
  rfl

private theorem place_transport {F L : Type u} [Field F] [Field L] [Algebra F L]
    (M N : CurveModel F L) (h : M = N) (x : closedPoints M.C) :
    M.placeOfPoint x = N.placeOfPoint (isoClosed (eqToIso (congrArg CurveModel.C h)) x) := by
  subst N
  rfl

theorem source_place (x : closedPoints (sourceModel K E).C) :
    (sourceModel K E).placeOfPoint x =
      CurveModel.gluedPlaceOfPoint K (CurveModel.towerGenerator K (L := E))
        (CurveModel.transcendental_towerGenerator K)
        (isoClosed (NormalizedModelCover.sourceIso K E) x) := by
  exact place_transport (sourceModel K E) _ (model_eq K E) x

def mapClosed (x : closedPoints (sourceModel K E).C) : closedPoints (baseModel K).C := by
  haveI := NormalizedModelCover.cover_isFinite K E
  refine ⟨NormalizedModelCover.cover K E x.1,?_⟩
  change IsClosed {NormalizedModelCover.cover K E x.1}
  simpa only [Set.image_singleton] using
    (NormalizedModelCover.cover K E).isClosedMap {x.1} x.2

local instance baseParameterNonzero : Fact ((RatFunc.X : RatFunc K) ≠ 0) := ⟨RatFunc.X_ne_zero⟩
local instance baseZeroFinite : FiniteDimensional K⟮(RatFunc.X : RatFunc K)⟯ (RatFunc K) := by
  simpa only [CurveModel.towerGenerator,Algebra.algebraMap_self,RingHom.id_apply] using
    (CurveModel.finiteDimensional_adjoin_towerGenerator K (L := RatFunc K)).1
local instance baseInfinityFinite : FiniteDimensional K⟮(RatFunc.X : RatFunc K)⁻¹⟯ (RatFunc K) := by
  simpa only [CurveModel.towerGenerator,Algebra.algebraMap_self,RingHom.id_apply] using
    (CurveModel.finiteDimensional_adjoin_towerGenerator K (L := RatFunc K)).2

/-- Point/place compatibility for the actual finite cover between canonical Scheme models. -/
theorem point_restrict (x : closedPoints (sourceModel K E).C) :
    ((sourceModel K E).placeOfPoint x).restrict (RatFunc K) =
      (baseModel K).placeOfPoint (mapClosed K E x) := by
  rw [source_place K E]
  have hb := source_place K (RatFunc K) (mapClosed K E x)
  simp only [CurveModel.towerGenerator,Algebra.algebraMap_self,RingHom.id_apply] at hb
  rw [hb]
  letI : FiniteDimensional K⟮NormalizationPointRestriction.inclusion (K := K) (E := E) (RatFunc.X : RatFunc K)⟯ E := sourceZeroFinite K E
  letI : FiniteDimensional K⟮(NormalizationPointRestriction.inclusion (K := K) (E := E) (RatFunc.X : RatFunc K))⁻¹⟯ E := sourceInfinityFinite K E
  have h := NormalizationPointRestriction.point_restrict (RatFunc.X : RatFunc K)
    RatFunc.transcendental_X (isoClosed (NormalizedModelCover.sourceIso K E) x)
  refine h.trans (congrArg (CurveModel.gluedPlaceOfPoint K (RatFunc.X : RatFunc K)
    RatFunc.transcendental_X) ?_)
  apply Subtype.ext
  have he : NormalizedModelCover.cover K E ≫ (NormalizedModelCover.baseIso K).hom =
      (NormalizedModelCover.sourceIso K E).hom ≫
        NormalizationCoverMap.cover (NormalizedModelCover.fieldInclusion K E) RatFunc.X := by
    simp only [NormalizedModelCover.cover,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact (congrArg (fun f => f x.1) he).symm

end FourCorner.NormalizedModelPointRestriction
#print axioms FourCorner.NormalizedModelPointRestriction.source_place

#print axioms FourCorner.NormalizedModelPointRestriction.point_restrict
