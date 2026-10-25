import NormalizationCoverMap
import FiniteNormalizationChartMaps

noncomputable section
namespace FourCorner.FiniteNormalizationCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IntermediateField
open FourCorner.NormalizationCoefficientMap FourCorner.NormalizationCoverMap
universe u
variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma zeroMap_parameter (φ : F →ₐ[K] E) (s : F) :
    zeroMap φ s (CurveModel.tChart K s) = CurveModel.tChart K (φ s) := by
  apply Subtype.val_injective
  rw [zeroMap_coe,CurveModel.coe_tChart,CurveModel.coe_tChart]
lemma infinityMap_parameter (φ : F →ₐ[K] E) (s : F) :
    infinityMap φ s (CurveModel.tInvChart K s) = CurveModel.tInvChart K (φ s) := by
  apply Subtype.val_injective
  rw [infinityMap_coe,CurveModel.coe_tInvChart,CurveModel.coe_tInvChart]
  exact map_inv₀ φ s

variable (φ : F →ₐ[K] E) (s : F) [Fact (s ≠ 0)]
local instance mapped_nonzero : Fact (φ s ≠ 0) :=
  ⟨fun h => (Fact.out : s ≠ 0) (φ.injective (h.trans (map_zero φ).symm))⟩

/-- The inverse image of the zero chart is exactly the source normalization zero chart. -/
theorem preimage_zero :
    (cover φ s) ⁻¹ᵁ (CurveModel.ι₀ K s).opensRange = (CurveModel.ι₀ K (φ s)).opensRange := by
  apply SetLike.ext
  intro x
  change cover φ s x ∈ Set.range (CurveModel.ι₀ K s).base ↔ x ∈ Set.range (CurveModel.ι₀ K (φ s)).base
  rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf K (φ s) x with ⟨p,rfl⟩|⟨p,rfl⟩
  · have hm : cover φ s ((CurveModel.ι₀ K (φ s)) p) =
        (CurveModel.ι₀ K s) (zeroSchemeMap φ s p) :=
      congrArg (fun m => m p) (zero_cover φ s)
    constructor
    · intro _; exact ⟨p,rfl⟩
    · intro _; rw [hm]; exact ⟨zeroSchemeMap φ s p,rfl⟩
  · have hm : cover φ s ((CurveModel.ιInf K (φ s)) p) =
        (CurveModel.ιInf K s) (infinitySchemeMap φ s p) :=
      congrArg (fun m => m p) (infinity_cover φ s)
    rw [hm,CurveModel.ιInf_mem_range_ι₀_iff,CurveModel.ιInf_mem_range_ι₀_iff]
    change infinityMap φ s (CurveModel.tInvChart K s) ∉ p.asIdeal ↔
      CurveModel.tInvChart K (φ s) ∉ p.asIdeal
    rw [infinityMap_parameter]

/-- The inverse image of the infinity chart is exactly the source normalization infinity chart. -/
theorem preimage_infinity :
    (cover φ s) ⁻¹ᵁ (CurveModel.ιInf K s).opensRange = (CurveModel.ιInf K (φ s)).opensRange := by
  apply SetLike.ext
  intro x
  change cover φ s x ∈ Set.range (CurveModel.ιInf K s).base ↔ x ∈ Set.range (CurveModel.ιInf K (φ s)).base
  rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf K (φ s) x with ⟨p,rfl⟩|⟨p,rfl⟩
  · have hm : cover φ s ((CurveModel.ι₀ K (φ s)) p) =
        (CurveModel.ι₀ K s) (zeroSchemeMap φ s p) :=
      congrArg (fun m => m p) (zero_cover φ s)
    rw [hm,CurveModel.ι₀_mem_range_ιInf_iff,CurveModel.ι₀_mem_range_ιInf_iff]
    change zeroMap φ s (CurveModel.tChart K s) ∉ p.asIdeal ↔
      CurveModel.tChart K (φ s) ∉ p.asIdeal
    rw [zeroMap_parameter]
  · have hm : cover φ s ((CurveModel.ιInf K (φ s)) p) =
        (CurveModel.ιInf K s) (infinitySchemeMap φ s p) :=
      congrArg (fun m => m p) (infinity_cover φ s)
    constructor
    · intro _; exact ⟨p,rfl⟩
    · intro _; rw [hm]; exact ⟨infinitySchemeMap φ s p,rfl⟩

theorem zero_isPullback :
    IsPullback (zeroSchemeMap φ s) (CurveModel.ι₀ K (φ s)) (CurveModel.ι₀ K s) (cover φ s) :=
  IsOpenImmersion.isPullback _ _ _ _ (zero_cover φ s) (preimage_zero φ s)
theorem infinity_isPullback :
    IsPullback (infinitySchemeMap φ s) (CurveModel.ιInf K (φ s)) (CurveModel.ιInf K s) (cover φ s) :=
  IsOpenImmersion.isPullback _ _ _ _ (infinity_cover φ s) (preimage_infinity φ s)

section CoverHelpers
variable (K0 F0 : Type u) [Field K0] [Field F0] [Algebra K0 F0] (t : F0) [Fact (t ≠ 0)]

def baseOpenCover : (CurveModel.glued K0 t).OpenCover :=
  .mkOfCovers Bool (fun b => if b then CurveModel.X₀ K0 t else CurveModel.XInf K0 t)
    (fun b => match b with | false => CurveModel.ιInf K0 t | true => CurveModel.ι₀ K0 t)
    (by
      intro x
      rcases CurveModel.mem_range_ι₀_or_mem_range_ιInf K0 t x with ⟨p,hp⟩|⟨p,hp⟩
      · exact ⟨true,p,hp⟩
      · exact ⟨false,p,hp⟩)
    (by intro b; cases b <;> infer_instance)
end CoverHelpers

lemma finite_pullback_of_square {U V X Y : Scheme.{u}} {g : U ⟶ V} {iU : U ⟶ X}
    {iV : V ⟶ Y} {f : X ⟶ Y} (hp : IsPullback g iU iV f) [IsFinite g] :
    IsFinite (pullback.snd f iV) := by
  rw [← hp.flip.isoPullback_inv_snd]
  infer_instance

/-- The genuine glued normalization cover is a finite Scheme morphism. -/
theorem cover_isFinite [CharZero K] [FiniteDimensional K⟮φ s⟯ E] [FiniteDimensional K⟮(φ s)⁻¹⟯ E] :
    IsFinite (cover φ s) := by
  haveI : IsFinite (zeroSchemeMap φ s) := FiniteNormalizationChartMaps.zeroSchemeMap_finite φ s
  haveI : IsFinite (infinitySchemeMap φ s) := FiniteNormalizationChartMaps.infinitySchemeMap_finite φ s
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) (baseOpenCover K F s)
  intro b
  cases b
  · change IsFinite (pullback.snd (cover φ s) (CurveModel.ιInf K s))
    exact finite_pullback_of_square (infinity_isPullback φ s)
  · change IsFinite (pullback.snd (cover φ s) (CurveModel.ι₀ K s))
    exact finite_pullback_of_square (zero_isPullback φ s)

#print axioms preimage_zero
#print axioms preimage_infinity
#print axioms zero_isPullback
#print axioms infinity_isPullback
#print axioms cover_isFinite
end FourCorner.FiniteNormalizationCover
