import NormalizationCoefficientMap
import Mathlib.AlgebraicGeometry.Morphisms.Finite

noncomputable section
namespace FourCorner.FiniteNormalizationChartMaps
open AlgebraicCurve AlgebraicGeometry IntermediateField
open FourCorner.NormalizationCoefficientMap
universe u
variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def singletonCoefficients (φ : F →ₐ[K] E) (s : F) (t : E) (ht : φ s=t) :
    Algebra.adjoin K ({s} : Set F) →ₐ[K] Algebra.adjoin K ({t} : Set E) :=
  coefficientMap φ _ _ (by simp [ht])

lemma singletonCoefficients_surjective (φ : F →ₐ[K] E) (s : F) (t : E) (ht : φ s=t) :
    Function.Surjective (singletonCoefficients φ s t ht) := by
  have heq : (Algebra.adjoin K ({s} : Set F)).map φ = Algebra.adjoin K ({t} : Set E) := by
    rw [AlgHom.map_adjoin]
    simp only [Set.image_singleton,ht]
  intro a
  have ha : (a : E) ∈ (Algebra.adjoin K ({s} : Set F)).map φ := heq.symm ▸ a.2
  obtain ⟨b,hb,hba⟩ := ha
  exact ⟨⟨b,hb⟩,Subtype.ext hba⟩

lemma singleton_square_value (φ : F →ₐ[K] E) (s : F) (t : E) (ht : φ s=t)
    (a : Algebra.adjoin K ({s} : Set F)) :
    (chartMap φ ({s} : Set F) ({t} : Set E) (by simp [ht])
      (algebraMap (Algebra.adjoin K ({s} : Set F)) (CurveModel.chartRing K ({s} : Set F)) a) : E) =
      (algebraMap (Algebra.adjoin K ({t} : Set E)) (CurveModel.chartRing K ({t} : Set E))
        (singletonCoefficients φ s t ht a) : E) := rfl

lemma singleton_square (φ : F →ₐ[K] E) (s : F) (t : E) (ht : φ s=t) :
    (chartMap φ ({s} : Set F) ({t} : Set E) (by simp [ht])).comp
      (algebraMap (Algebra.adjoin K ({s} : Set F)) (CurveModel.chartRing K ({s} : Set F))) =
    (algebraMap (Algebra.adjoin K ({t} : Set E)) (CurveModel.chartRing K ({t} : Set E))).comp
      (singletonCoefficients φ s t ht).toRingHom :=
  RingHom.ext fun a => Subtype.val_injective (singleton_square_value φ s t ht a)

/-- The actual normalization-chart ring map is finite, deduced from the true polynomial
coefficient surjection and the finiteness of integral closure in the given finite field extension. -/
theorem singleton_chartMap_finite [CharZero K] (φ : F →ₐ[K] E) (s : F) (t : E) (ht : φ s=t)
    [FiniteDimensional K⟮t⟯ E] :
    (chartMap φ ({s} : Set F) ({t} : Set E) (by simp [ht])).Finite := by
  haveI : Module.Finite (Algebra.adjoin K ({t} : Set E)) (CurveModel.chartRing K ({t} : Set E)) :=
    CurveModel.finite_chartRing K t
  have hs : (algebraMap (Algebra.adjoin K ({t} : Set E))
      (CurveModel.chartRing K ({t} : Set E))).Finite := by
    simpa only [RingHom.finite_algebraMap] using
      (inferInstance : Module.Finite (Algebra.adjoin K ({t} : Set E)) (CurveModel.chartRing K ({t} : Set E)))
  have hc := RingHom.Finite.of_surjective (singletonCoefficients φ s t ht).toRingHom
    (singletonCoefficients_surjective φ s t ht)
  have hh := hs.comp hc
  rw [← singleton_square φ s t ht] at hh
  exact RingHom.Finite.of_comp_finite hh

theorem zeroMap_finite [CharZero K] (φ : F →ₐ[K] E) (s : F) [FiniteDimensional K⟮φ s⟯ E] :
    (zeroMap φ s).Finite := singleton_chartMap_finite φ s (φ s) rfl

theorem infinityMap_finite [CharZero K] (φ : F →ₐ[K] E) (s : F) [FiniteDimensional K⟮(φ s)⁻¹⟯ E] :
    (infinityMap φ s).Finite := singleton_chartMap_finite φ s⁻¹ ((φ s)⁻¹) (map_inv₀ φ s)

theorem zeroSchemeMap_finite [CharZero K] (φ : F →ₐ[K] E) (s : F) [FiniteDimensional K⟮φ s⟯ E] :
    IsFinite (Spec.map (CommRingCat.ofHom (zeroMap φ s))) :=
  (IsFinite.SpecMap_iff _).mpr (zeroMap_finite φ s)
theorem infinitySchemeMap_finite [CharZero K] (φ : F →ₐ[K] E) (s : F) [FiniteDimensional K⟮(φ s)⁻¹⟯ E] :
    IsFinite (Spec.map (CommRingCat.ofHom (infinityMap φ s))) :=
  (IsFinite.SpecMap_iff _).mpr (infinityMap_finite φ s)

#print axioms singletonCoefficients_surjective
#print axioms singleton_square
#print axioms zeroSchemeMap_finite
#print axioms infinitySchemeMap_finite
end FourCorner.FiniteNormalizationChartMaps
