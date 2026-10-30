import NormalizedModelPointRestriction

noncomputable section
namespace FourCorner.NormalizationGenericPoint
open CategoryTheory AlgebraicGeometry AlgebraicCurve IntermediateField
universe u
variable (K L : Type u) [Field K] [CharZero K] [Field L] [Algebra K L]
variable (s : L) [Fact (s ≠ 0)] [FiniteDimensional K⟮s⟯ L]
    [FiniteDimensional K⟮s⁻¹⟯ L]
set_option maxHeartbeats 1000000

/-- The normalization field point is the genuine generic point, because its
chart-ring embedding is the actual fraction-field embedding. -/
theorem fieldPoint_generic :
    NormalizationCoverField.fieldPoint K L s (IsLocalRing.closedPoint L) =
      genericPoint (CurveModel.glued K s) := by
  let R := CurveModel.chartRing K ({s} : Set L)
  have hx : Spec.map (CommRingCat.ofHom (algebraMap R L)) (IsLocalRing.closedPoint L) =
      genericPoint (Spec (.of R)) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) (IsLocalRing.maximalIdeal L) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    apply le_antisymm ?_ bot_le
    intro a ha
    change algebraMap R L a = 0 at ha
    exact (Ideal.mem_bot).mpr ((IsFractionRing.injective R L) (ha.trans (map_zero _).symm))
  change CurveModel.ι₀ K s (Spec.map (CommRingCat.ofHom (algebraMap R L)) (IsLocalRing.closedPoint L)) = _
  rw [hx]
  exact genericPoint_eq_of_isOpenImmersion (CurveModel.ι₀ K s)

theorem fieldPoint_dominant : IsDominant (NormalizationCoverField.fieldPoint K L s) := by
  constructor
  intro x
  have hr : ({genericPoint (CurveModel.glued K s)} : Set (CurveModel.glued K s)) ⊆
      Set.range (NormalizationCoverField.fieldPoint K L s) := by
    apply Set.singleton_subset_iff.mpr
    exact ⟨IsLocalRing.closedPoint L,fieldPoint_generic K L s⟩
  have hc := closure_mono hr
  rw [show closure ({genericPoint (CurveModel.glued K s)} : Set (CurveModel.glued K s)) = Set.univ from genericPoint_spec _] at hc
  exact hc trivial
end FourCorner.NormalizationGenericPoint
#print axioms FourCorner.NormalizationGenericPoint.fieldPoint_generic
#print axioms FourCorner.NormalizationGenericPoint.fieldPoint_dominant
