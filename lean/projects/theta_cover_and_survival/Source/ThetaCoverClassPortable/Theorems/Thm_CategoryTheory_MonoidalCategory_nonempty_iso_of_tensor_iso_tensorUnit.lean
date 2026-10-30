import Mathlib.CategoryTheory.Monoidal.Braided.Basic

noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
universe u v

/-- Right tensor inverses of isomorphic objects are isomorphic in a braided
monoidal category. This is the actual missing cancellation body, not an axiom. -/
theorem CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    {A A' B C : D} (e : A ≅ A') (hAB : Nonempty (A ⊗ B ≅ 𝟙_ D))
    (hAC : Nonempty (A' ⊗ C ≅ 𝟙_ D)) :
    Nonempty (B ≅ C) := by
  obtain ⟨iAB⟩ := hAB
  obtain ⟨iAC⟩ := hAC
  exact ⟨(λ_ B).symm ≪≫ (iAC.symm ⊗ᵢ Iso.refl B) ≪≫
    (α_ A' C B) ≪≫ (Iso.refl A' ⊗ᵢ β_ C B) ≪≫ (α_ A' B C).symm ≪≫
    ((e.symm ⊗ᵢ Iso.refl B) ⊗ᵢ Iso.refl C) ≪≫ (iAB ⊗ᵢ Iso.refl C) ≪≫ λ_ C⟩

#print axioms CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
