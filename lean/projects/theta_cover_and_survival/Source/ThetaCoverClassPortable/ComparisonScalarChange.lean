import ThetaCoverClassPortable.LocalComparisonFree
import Mathlib.RingTheory.Flat.Localization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
namespace FourCorner.QuotientLocalFree
universe u
variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra A B]

/-- Scalar extension of the ACTUAL comparison, using the two genuine tensor
cancellation isomorphisms. No flatness hypothesis is needed for this construction. -/
def comparisonBaseChange (S : Type u) [CommRing S] [Algebra C S]
    (Can : A ⊗[C] A →ₐ[A] B) :
    letI : Algebra A (S ⊗[C] A) := Algebra.TensorProduct.rightAlgebra
    (S ⊗[C] A) ⊗[S] (S ⊗[C] A) →ₐ[S ⊗[C] A] (S ⊗[C] A) ⊗[A] B := by
  let AS := S ⊗[C] A
  letI : Algebra A AS := Algebra.TensorProduct.rightAlgebra
  let E := (Algebra.TensorProduct.cancelBaseChange C S AS AS A).trans
    (Algebra.TensorProduct.cancelBaseChange C A AS AS A).symm
  exact (Algebra.TensorProduct.map (AlgHom.id AS AS) Can).comp E.toAlgHom

theorem comparisonBaseChange_surjective (S : Type u) [CommRing S] [Algebra C S]
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can) :
    letI : Algebra A (S ⊗[C] A) := Algebra.TensorProduct.rightAlgebra
    Function.Surjective (comparisonBaseChange S Can) := by
  let AS := S ⊗[C] A
  letI : Algebra A AS := Algebra.TensorProduct.rightAlgebra
  let E := (Algebra.TensorProduct.cancelBaseChange C S AS AS A).trans
    (Algebra.TensorProduct.cancelBaseChange C A AS AS A).symm
  let ψ := Algebra.TensorProduct.map (AlgHom.id AS AS) Can
  have hψ : Function.Surjective ψ := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero ψ⟩
    | tmul a b =>
      obtain ⟨z, rfl⟩ := hCan b
      exact ⟨a ⊗ₜ[A] z, by simp [ψ]⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add ψ x' y'⟩
  exact hψ.comp E.surjective

/-- Injectivity survives FLAT SCALAR EXTENSION S/C; this does not assume A/C flat. -/
theorem inclusion_injective_after_flat_scalar_change (S : Type u) [CommRing S] [Algebra C S]
    [Module.Flat C S] (hinj : Function.Injective (algebraMap C A)) :
    Function.Injective (algebraMap S (S ⊗[C] A)) := by
  have hh := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (Algebra.linearMap C A) hinj
  intro x y hxy
  have ht : (x ⊗ₜ[C] (1 : C)) = y ⊗ₜ[C] (1 : C) := by
    apply hh
    simpa only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using hxy
  have hz := congrArg (TensorProduct.rid C S) ht
  simpa using hz
end FourCorner.QuotientLocalFree
