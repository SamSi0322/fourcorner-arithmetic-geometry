import ThetaCoverClassPortable.ModuleSurjectiveTensor
import ThetaCoverClassPortable.FiniteRelationOrbitTensor

namespace FourCorner.RelativeTensorCancel
noncomputable section
open scoped TensorProduct
universe u
variable (K A D B M : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]
variable [AddCommGroup M] [Module K M] [Module A M] [Module D M]
variable [IsScalarTower K A M] [IsScalarTower K D M] [IsScalarTower A D M]

/-- True relative tensor cancellation on the SAME module M. It does NOT
map M into a quotient ring or discard a nilpotent ideal layer. -/
def relativeCancel : ((D ⊗[A] B) ⊗[D] M) ≃ₗ[K] B ⊗[A] M :=
  ((TensorProduct.comm D (D ⊗[A] B) M).restrictScalars K).trans
    (((TensorProduct.AlgebraTensorModule.cancelBaseChange A D D M B).restrictScalars K).trans
      ((TensorProduct.comm A M B).restrictScalars K))

 theorem relativeCancel_tmul (d : D) (b : B) (m : M) :
    relativeCancel K A D B M ((d ⊗ₜ[A] b) ⊗ₜ[D] m)=b ⊗ₜ[A] (d • m) := by rfl

 theorem relativeCancel_symm_tmul (b : B) (m : M) :
    (relativeCancel K A D B M).symm (b ⊗ₜ[A] m)=((1 : D) ⊗ₜ[A] b) ⊗ₜ[D] m := by rfl

#print axioms relativeCancel
#print axioms relativeCancel_tmul
#print axioms relativeCancel_symm_tmul
end
end FourCorner.RelativeTensorCancel
