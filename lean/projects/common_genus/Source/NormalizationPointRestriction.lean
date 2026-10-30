import NormalizationPlaceRestriction

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory IntermediateField
namespace FourCorner.NormalizationPointRestriction
open NormalizationCoverMap NormalizationCoefficientMap
universe u
variable {K F E : Type u} [Field K] [CharZero K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E]
variable (s : F) [Fact (s ≠ 0)]
variable [FiniteDimensional K⟮s⟯ F] [FiniteDimensional K⟮s⁻¹⟯ F]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

abbrev inclusion : F →ₐ[K] E := IsScalarTower.toAlgHom K F E
variable [FiniteDimensional K⟮inclusion (K := K) (E := E) s⟯ E]
    [FiniteDimensional K⟮(inclusion (K := K) (E := E) s)⁻¹⟯ E]
local instance sourceParameterNonzero : Fact (inclusion (K := K) (F := F) (E := E) s ≠ 0) :=
  ⟨fun h => (Fact.out : s ≠ 0) ((algebraMap F E).injective (h.trans (map_zero (algebraMap F E)).symm))⟩

abbrev map := NormalizationCoverMap.cover (inclusion (K := K) (F := F) (E := E)) s

def mapClosed (x : closedPoints (CurveModel.glued K (inclusion (K := K) (E := E) s))) :
    closedPoints (CurveModel.glued K s) := by
  haveI := FiniteNormalizationCover.cover_isFinite (inclusion (K := K) (E := E)) s
  refine ⟨map s x.1,?_⟩
  change IsClosed {(map s) x.1}
  have h := (map s).isClosedMap {x.1} x.2
  simpa only [Set.image_singleton] using h

/-- On the actual zero normalization chart, the map of closed points is exactly
restriction of genuine function-field places, including its prime contraction. -/
theorem zero_point_restrict (hs : Transcendental K s)
    (x : CurveModel.X₀ K (inclusion (K := K) (E := E) s))
    (hx : CurveModel.ι₀ K (inclusion (K := K) (E := E) s) x ∈
      closedPoints (CurveModel.glued K (inclusion (K := K) (E := E) s))) :
    (CurveModel.gluedPlaceOfPoint K (inclusion (K := K) (E := E) s)
      ((transcendental_algebraMap_iff (algebraMap F E).injective).mpr hs)
        ⟨CurveModel.ι₀ K (inclusion (K := K) (E := E) s) x,hx⟩).restrict F =
      CurveModel.gluedPlaceOfPoint K s hs
        (mapClosed s ⟨CurveModel.ι₀ K (inclusion (K := K) (E := E) s) x,hx⟩) := by
  let hE : Transcendental K (inclusion (K := K) (E := E) s) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr hs
  let y := zeroSchemeMap (inclusion (K := K) (E := E)) s x
  have heq : map s (CurveModel.ι₀ K (inclusion (K := K) (E := E) s) x) = CurveModel.ι₀ K s y :=
    congrArg (fun f => f x) (NormalizationCoverMap.zero_cover (inclusion (K := K) (E := E)) s)
  have hy : CurveModel.ι₀ K s y ∈ closedPoints (CurveModel.glued K s) := by
    rw [← heq]
    exact (mapClosed s ⟨_,hx⟩).2
  have hp : mapClosed s ⟨_,hx⟩ = (⟨CurveModel.ι₀ K s y,hy⟩ : closedPoints (CurveModel.glued K s)) :=
    Subtype.ext heq
  rw [hp]
  erw [CurveModel.gluedPlaceOfPoint_ι₀,CurveModel.gluedPlaceOfPoint_ι₀]
  apply NormalizationPlaceRestriction.heightOne_restrict
    (CurveModel.chartRing K ({s} : Set F))
    (CurveModel.chartRing K ({inclusion (K := K) (E := E) s} : Set E))
    (zeroMap (inclusion (K := K) (E := E)) s)
  · intro a
    exact zeroMap_coe (inclusion (K := K) (E := E)) s a
  · rfl


/-- The infinity-chart case retains the reciprocal parameter and its prime contraction. -/
theorem infinity_point_restrict (hs : Transcendental K s)
    (x : CurveModel.XInf K (inclusion (K := K) (E := E) s))
    (hx : CurveModel.ιInf K (inclusion (K := K) (E := E) s) x ∈
      closedPoints (CurveModel.glued K (inclusion (K := K) (E := E) s)))
    (hnot : CurveModel.ιInf K (inclusion (K := K) (E := E) s) x ∉
      Set.range (CurveModel.ι₀ K (inclusion (K := K) (E := E) s))) :
    (CurveModel.gluedPlaceOfPoint K (inclusion (K := K) (E := E) s)
      ((transcendental_algebraMap_iff (algebraMap F E).injective).mpr hs)
        ⟨CurveModel.ιInf K (inclusion (K := K) (E := E) s) x,hx⟩).restrict F =
      CurveModel.gluedPlaceOfPoint K s hs
        (mapClosed s ⟨CurveModel.ιInf K (inclusion (K := K) (E := E) s) x,hx⟩) := by
  let hE : Transcendental K (inclusion (K := K) (E := E) s) :=
    (transcendental_algebraMap_iff (algebraMap F E).injective).mpr hs
  let y := infinitySchemeMap (inclusion (K := K) (E := E)) s x
  have heq : map s (CurveModel.ιInf K (inclusion (K := K) (E := E) s) x) = CurveModel.ιInf K s y :=
    congrArg (fun f => f x) (NormalizationCoverMap.infinity_cover (inclusion (K := K) (E := E)) s)
  have hy : CurveModel.ιInf K s y ∈ closedPoints (CurveModel.glued K s) := by
    rw [← heq]
    exact (mapClosed s ⟨_,hx⟩).2
  have hp : mapClosed s ⟨_,hx⟩ = (⟨CurveModel.ιInf K s y,hy⟩ : closedPoints (CurveModel.glued K s)) :=
    Subtype.ext heq
  have hmem : CurveModel.tInvChart K (inclusion (K := K) (E := E) s) ∈ x.asIdeal := by
    by_contra hn
    exact hnot ((CurveModel.ιInf_mem_range_ι₀_iff K (inclusion (K := K) (E := E) s) x).mpr hn)
  have hbaseNot : CurveModel.ιInf K s y ∉ Set.range (CurveModel.ι₀ K s) := by
    intro hy0
    have hn := (CurveModel.ιInf_mem_range_ι₀_iff K s y).mp hy0
    apply hn
    change infinityMap (inclusion (K := K) (E := E)) s (CurveModel.tInvChart K s) ∈ x.asIdeal
    rw [FiniteNormalizationCover.infinityMap_parameter]
    exact hmem
  rw [hp]
  have hsrc := CurveModel.gluedPlaceOfPoint_of_not_mem K (inclusion (K := K) (E := E) s) hE ⟨_,hx⟩ hnot x rfl
  have hdst := CurveModel.gluedPlaceOfPoint_of_not_mem K s hs ⟨_,hy⟩ hbaseNot y rfl
  erw [hsrc,hdst]
  apply NormalizationPlaceRestriction.heightOne_restrict
    (CurveModel.chartRing K ({s⁻¹} : Set F))
    (CurveModel.chartRing K ({(inclusion (K := K) (E := E) s)⁻¹} : Set E))
    (infinityMap (inclusion (K := K) (E := E)) s)
  · intro a
    exact infinityMap_coe (inclusion (K := K) (E := E)) s a
  · rfl

/-- The actual native finite normalization morphism commutes with the point/place
bijections on every closed point, not merely at a generic function-field point. -/
theorem point_restrict (hs : Transcendental K s)
    (x : closedPoints (CurveModel.glued K (inclusion (K := K) (E := E) s))) :
    (CurveModel.gluedPlaceOfPoint K (inclusion (K := K) (E := E) s)
      ((transcendental_algebraMap_iff (algebraMap F E).injective).mpr hs) x).restrict F =
      CurveModel.gluedPlaceOfPoint K s hs (mapClosed s x) := by
  obtain ⟨x,hx⟩ := x
  by_cases h0 : x ∈ Set.range (CurveModel.ι₀ K (inclusion (K := K) (E := E) s))
  · obtain ⟨x0,rfl⟩ := h0
    exact zero_point_restrict s hs x0 hx
  · obtain ⟨xi,rfl⟩ := CurveModel.mem_range_ιInf_of_not_mem_range_ι₀ K (inclusion (K := K) (E := E) s) h0
    exact infinity_point_restrict s hs xi hx h0

end FourCorner.NormalizationPointRestriction
#print axioms FourCorner.NormalizationPointRestriction.zero_point_restrict

#print axioms FourCorner.NormalizationPointRestriction.infinity_point_restrict
#print axioms FourCorner.NormalizationPointRestriction.point_restrict
