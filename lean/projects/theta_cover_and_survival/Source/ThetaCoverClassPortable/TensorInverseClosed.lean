import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.MonoidalCategory
namespace FourCorner.FieldZeroDivisor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

private def tensorEquivalence {L N : C} (e : L ⊗ N ≅ 𝟙_ C) : C ≌ C := by
  let e' : N ⊗ L ≅ 𝟙_ C := (β_ N L) ≪≫ e
  let η : 𝟭 C ≅ tensorLeft L ⋙ tensorLeft N :=
    (leftUnitorNatIso C).symm ≪≫ (tensoringLeft C).mapIso e'.symm ≪≫ tensorLeftTensor N L
  let ε : tensorLeft N ⋙ tensorLeft L ≅ 𝟭 C :=
    (tensorLeftTensor L N).symm ≪≫ (tensoringLeft C).mapIso e ≪≫ leftUnitorNatIso C
  exact CategoryTheory.Equivalence.mk (tensorLeft L) (tensorLeft N) η ε

 theorem tensorLeft_isEquivalence {L N : C} (e : L ⊗ N ≅ 𝟙_ C) :
    (tensorLeft L).IsEquivalence := (tensorEquivalence e).isEquivalence_functor

 theorem evaluation_isIso [MonoidalClosed C] {L N : C} (e : L ⊗ N ≅ 𝟙_ C) (F : C) :
    IsIso ((ihom.ev L).app F) := by
  letI := tensorLeft_isEquivalence e
  exact inferInstanceAs (IsIso ((ihom.adjunction L).counit.app F))

 theorem bidual_isIso [MonoidalClosed C] {L N : C} (e : L ⊗ N ≅ 𝟙_ C) :
    IsIso (MonoidalClosed.curry
      ((β_ ((ihom L).obj (𝟙_ C)) L).hom ≫ (ihom.ev L).app (𝟙_ C))) := by
  letI := evaluation_isIso e (𝟙_ C)
  let D := (ihom L).obj (𝟙_ C)
  let e' : D ⊗ L ≅ 𝟙_ C := (β_ D L) ≪≫ asIso ((ihom.ev L).app (𝟙_ C))
  letI := tensorLeft_isEquivalence e'
  rw [MonoidalClosed.curry_eq]
  exact inferInstanceAs (IsIso ((ihom.adjunction D).unit.app L ≫
    (ihom D).map ((β_ D L).hom ≫ (ihom.ev L).app (𝟙_ C))))
end FourCorner.FieldZeroDivisor

namespace CategoryTheory.MonoidalClosed
 theorem isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    {L N : C} (e : L ⊗ N ≅ 𝟙_ C) :
    (∀ F : C, IsIso ((ihom.ev L).app F)) ∧
      IsIso (curry ((β_ ((ihom L).obj (𝟙_ C)) L).hom ≫ (ihom.ev L).app (𝟙_ C))) :=
  ⟨FourCorner.FieldZeroDivisor.evaluation_isIso e, FourCorner.FieldZeroDivisor.bidual_isIso e⟩
end CategoryTheory.MonoidalClosed
