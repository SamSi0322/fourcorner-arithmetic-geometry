import ThetaCoverClassPortable.RelativeCancellationNaturality

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.PairCoactionTransfer
open FourCorner.RelativeTensorCancel
universe u
variable (K A D B M : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]
variable [AddCommGroup M] [Module K M] [Module A M] [Module D M]
variable [IsScalarTower K A M] [IsScalarTower K D M] [IsScalarTower A D M]

/-- Multiplication in the TARGET pair coordinate becomes multiplication on
the LEFT output factor under true relative cancellation. -/
theorem pairCancel_target_mul (d : D) (z : D ⊗[K] D) (m : M) :
    relativeCancel K K D D M ((((1 : D) ⊗ₜ[K] d) * z) ⊗ₜ[D] m) =
      d • relativeCancel K K D D M (z ⊗ₜ[D] m) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [mul_zero, TensorProduct.zero_tmul, map_zero, smul_zero]
  | add x y hx hy =>
    simp only [mul_add, TensorProduct.add_tmul, map_add, smul_add, hx, hy]
  | tmul x y =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, relativeCancel_tmul,
      TensorProduct.smul_tmul', smul_eq_mul]

/-- The proved target-coordinate formula makes beta target-A linear.
The final coaction/cocycle is NOT a hypothesis here. -/
theorem sourceCoordinates_target_smul
    (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, e ((1 : D) ⊗ₜ[A] t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (a : A) (z : B ⊗[A] M) :
    sourceCoordinates K A D B M e (t a • z) =
      algebraMap A D a • sourceCoordinates K A D B M e z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul b m =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, sourceCoordinates_tmul,
      sourceCoordinates_tmul]
    have hm : e ((1 : D) ⊗ₜ[A] (t a * b)) =
        ((1 : D) ⊗ₜ[K] algebraMap A D a) * e ((1 : D) ⊗ₜ[A] b) := by
      rw [show ((1 : D) ⊗ₜ[A] (t a * b)) =
        ((1 : D) ⊗ₜ[A] t a) * ((1 : D) ⊗ₜ[A] b) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], map_mul, ht]
    rw [hm]
    exact pairCancel_target_mul K D M _ _ _

end FourCorner.PairCoactionTransfer
