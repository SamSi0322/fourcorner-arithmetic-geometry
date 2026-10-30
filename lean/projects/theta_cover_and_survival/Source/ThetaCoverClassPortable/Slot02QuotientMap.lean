import ThetaCoverClassPortable.Slot02QuotientGrading

/-!
The bundled graded quotient map of the actual ideal quotient. This is a new
wrapper around the replayed generic construction, not an upstream source edit.
-/

namespace HomogeneousIdealQuotientGrading

variable {ι A σ : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]
  (J : HomogeneousIdeal 𝒜)

/-- The actual ideal quotient map, bundled as a graded ring homomorphism. -/
def quotientGradedMap : 𝒜 →+*ᵍ quotGrading 𝒜 J.toIdeal where
  __ := Ideal.Quotient.mk J.toIdeal
  map_mem h := mk_mem_quotGrading 𝒜 J.toIdeal h

@[simp] theorem quotientGradedMap_apply (a : A) :
    quotientGradedMap 𝒜 J a = Ideal.Quotient.mk J.toIdeal a := rfl

/-- Surjectivity is that of the actual quotient map. -/
theorem quotientGradedMap_surjective : Function.Surjective (quotientGradedMap 𝒜 J) :=
  Ideal.Quotient.mk_surjective

/-- The quotient kills precisely the given homogeneous ideal. -/
theorem quotientGradedMap_eq_zero_iff (a : A) :
    quotientGradedMap 𝒜 J a = 0 ↔ a ∈ J.toIdeal :=
  Ideal.Quotient.eq_zero_iff_mem

end HomogeneousIdealQuotientGrading

#print axioms HomogeneousIdealQuotientGrading.quotGradingGradedRingOfHomogeneous
#print axioms HomogeneousIdealQuotientGrading.quotientGradedMap
#print axioms HomogeneousIdealQuotientGrading.quotientGradedMap_surjective
#print axioms HomogeneousIdealQuotientGrading.quotientGradedMap_eq_zero_iff
