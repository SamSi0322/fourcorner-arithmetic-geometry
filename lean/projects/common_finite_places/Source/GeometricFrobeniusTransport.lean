import GeometricTensorGeneration

noncomputable section
open scoped TensorProduct
namespace FourCorner.GeometricTensorFrobenius
variable (k L F E : Type*) [Field k] [Fintype k] [Field L] [Field F] [Field E]
  [Algebra k L] [Algebra k F] [Algebra L E] [IsDomain (L ⊗[k] F)]
variable (e : FractionRing (L ⊗[k] F) ≃ₐ[L] E)
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def imageHom : F →+* E := e.toRingHom.comp (sourceInclusion k L F).toRingHom
abbrev imageAlgebra : Algebra F E := (imageHom k L F E e).toAlgebra

def transportedFrobenius : E →ₐ[L] E :=
  e.toAlgHom.comp ((geometricFrobenius k L F).comp e.symm.toAlgHom)

theorem transportedFrobenius_image (x : F) :
    transportedFrobenius k L F E e (imageHom k L F E e x) =
      imageHom k L F E e (x^(Nat.card k)) := by
  change e (geometricFrobenius k L F (e.symm (e (sourceInclusion k L F x)))) =
    e (sourceInclusion k L F (x^(Nat.card k)))
  rw [AlgEquiv.symm_apply_apply,geometricFrobenius_source]
  simp only [Nat.card_eq_fintype_card]

theorem image_generates : IntermediateField.adjoin L (Set.range (imageHom k L F E e)) = ⊤ := by
  let S := IntermediateField.adjoin L (Set.range (imageHom k L F E e))
  have h : IntermediateField.adjoin L (Set.range (sourceInclusion k L F)) ≤ S.comap e.toAlgHom := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨x,rfl⟩
    exact IntermediateField.subset_adjoin L _ ⟨x,rfl⟩
  rw [source_generates k L F] at h
  apply top_unique
  intro z _
  obtain ⟨a,rfl⟩ := e.surjective z
  exact h (show a ∈ (⊤ : IntermediateField L (FractionRing (L ⊗[k] F))) by trivial)

theorem image_algebra_generates :
    letI := imageAlgebra k L F E e
    IntermediateField.adjoin L (Set.range (algebraMap F E)) = ⊤ := by
  letI := imageAlgebra k L F E e
  change IntermediateField.adjoin L (Set.range (imageHom k L F E e)) = ⊤
  exact image_generates k L F E e

theorem transportedFrobenius_algebraMap :
    letI := imageAlgebra k L F E e
    ∀ x : F, transportedFrobenius k L F E e (algebraMap F E x) = algebraMap F E (x^(Nat.card k)) := by
  letI := imageAlgebra k L F E e
  intro x
  exact transportedFrobenius_image k L F E e x

end FourCorner.GeometricTensorFrobenius
#print axioms FourCorner.GeometricTensorFrobenius.transportedFrobenius_algebraMap
#print axioms FourCorner.GeometricTensorFrobenius.image_algebra_generates
