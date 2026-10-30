import ThetaCoverClassPortable.RelativeTensorCancel

namespace FourCorner.RelativeTensorCancel
noncomputable section
open scoped TensorProduct
universe u
variable (K A D B M : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]
variable [AddCommGroup M] [Module K M] [Module A M] [Module D M]
variable [IsScalarTower K A M] [IsScalarTower K D M] [IsScalarTower A D M]

/-- Relative tensor cancellation through an ACTUAL over-D pair algebra
isomorphism. Later e is the previously PROVED original orbit equivalence. -/
def sourceCoordinates (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) :
    B ⊗[A] M ≃ₗ[K] D ⊗[K] M :=
  (relativeCancel K A D B M).symm.trans
    (((TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl D M)).restrictScalars K).trans
      (relativeCancel K K D D M))

 theorem sourceCoordinates_tmul (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (b : B) (m : M) :
    sourceCoordinates K A D B M e (b ⊗ₜ[A] m)=
      relativeCancel K K D D M (e ((1 : D) ⊗ₜ[A] b) ⊗ₜ[D] m) := by rfl

 theorem sourceCoordinates_one_tmul (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (m : M) :
    sourceCoordinates K A D B M e ((1 : B) ⊗ₜ[A] m)=(1 : D) ⊗ₜ[K] m := by
  rw [sourceCoordinates_tmul]
  have h1 : e ((1 : D) ⊗ₜ[A] (1 : B))=((1 : D) ⊗ₜ[K] (1 : D)) := by
    change e 1=1
    exact map_one e
  rw [h1,relativeCancel_tmul,one_smul]

#print axioms sourceCoordinates
#print axioms sourceCoordinates_tmul
#print axioms sourceCoordinates_one_tmul
end
end FourCorner.RelativeTensorCancel
