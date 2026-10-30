import ThetaCoverClassPortable.CoactionEqualizer

set_option autoImplicit false
open TensorProduct

namespace Module.FaithfullyFlat

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

theorem tensorUnit_injective [Module.FaithfullyFlat R S] :
    Function.Injective (TensorProduct.mk R S N 1) := by
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S
    (TensorProduct.mk R S N 1)).mp
  have h : ∀ x : S ⊗[R] N,
      tensorAction (R := R) ((TensorProduct.mk R S N 1).lTensor S x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => simp [smul_tmul']
    | add x y hx hy => simp [hx, hy]
  exact Function.LeftInverse.injective h

/-- For an injective coaction the cocycle equation already forces counitality. -/
theorem counit_of_coassoc_of_injective (ρ : N →ₗ[S] S ⊗[R] N)
    (hinj : Function.Injective ρ)
    (hcoassoc : ∀ n,
      (ρ.restrictScalars R).lTensor S (ρ n) =
        (TensorProduct.mk R S N 1).lTensor S (ρ n)) :
    ∀ n, tensorAction (R := R) (ρ n) = n := by
  have h₁ : ∀ x : S ⊗[R] N,
      tensorAction (R := R) ((ρ.restrictScalars R).lTensor S x) =
        ρ (tensorAction (R := R) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => simp
    | add x y hx hy => simp [hx, hy]
  have h₂ : ∀ x : S ⊗[R] N,
      tensorAction (R := R) ((TensorProduct.mk R S N 1).lTensor S x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => simp [smul_tmul']
    | add x y hx hy => simp [hx, hy]
  intro n
  apply hinj
  rw [← h₁, hcoassoc, h₂]

end Module.FaithfullyFlat
