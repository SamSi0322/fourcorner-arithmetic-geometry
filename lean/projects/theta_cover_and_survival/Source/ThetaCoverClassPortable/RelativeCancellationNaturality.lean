import ThetaCoverClassPortable.PairSourceCoordinates

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.PairCoactionTransfer
open FourCorner.RelativeTensorCancel
universe u
variable (K A D B M N : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]
variable [AddCommGroup M] [Module K M] [Module A M] [Module D M]
variable [IsScalarTower K A M] [IsScalarTower K D M] [IsScalarTower A D M]
variable [AddCommGroup N] [Module K N] [Module A N] [Module D N]
variable [IsScalarTower K A N] [IsScalarTower K D N] [IsScalarTower A D N]

/-- True relative tensor cancellation is natural in the retained D-module.
No map of M or N into D, or equality of coactions, is assumed. -/
theorem relativeCancel_natural (f : M →ₗ[D] N) (z : (D ⊗[A] B) ⊗[D] M) :
    relativeCancel K A D B N
        (TensorProduct.map (LinearMap.id : D ⊗[A] B →ₗ[D] D ⊗[A] B) f z) =
      TensorProduct.map (LinearMap.id : B →ₗ[A] B) (f.restrictScalars A)
        (relativeCancel K A D B M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x m =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul d b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, relativeCancel_tmul,
        LinearMap.restrictScalars_apply, map_smul]

/-- The actual pair-source coordinates are natural in a D-linear map of
retained modules. The source/target tensor order is unchanged. -/
theorem sourceCoordinates_natural (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D)
    (f : M →ₗ[D] N) (z : B ⊗[A] M) :
    sourceCoordinates K A D B N e
        (TensorProduct.map (LinearMap.id : B →ₗ[A] B) (f.restrictScalars A) z) =
      TensorProduct.map (LinearMap.id : D →ₗ[K] D) (f.restrictScalars K)
        (sourceCoordinates K A D B M e z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m =>
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply,
      sourceCoordinates_tmul] using
      relativeCancel_natural K K D D M N f (e ((1 : D) ⊗ₜ[A] b) ⊗ₜ[D] m)

end FourCorner.PairCoactionTransfer
