import ThetaCoverClassPortable.PairSourceCoordinates
import ThetaCoverClassPortable.FlatIdealTensorEquiv

namespace FourCorner.RelativeTensorCancel
noncomputable section
open scoped TensorProduct
universe u
variable (K A D B : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]
variable (J : Ideal A) [Module D J]
variable [IsScalarTower K D J] [IsScalarTower A D J]

/-- Coordinates on the ACTUAL extended ideal J·B⊂B, from the genuine
flat ideal embedding and an actual original pair algebra isomorphism.
The module J itself is retained; no image in D is taken. -/
def idealCoordinates [Module.Flat A B] (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) :
    Ideal.map (algebraMap A B) J ≃ₗ[K] D ⊗[K] J :=
  ((FourCorner.FlatIdealTensorEquiv.idealTensorEquiv (S:=B) J).symm.restrictScalars K).trans
    (sourceCoordinates K A D B J e)

 theorem idealCoordinates_source [Module.Flat A B] (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (j : J) :
    idealCoordinates K A D B J e
      ⟨algebraMap A B (j : A),Ideal.mem_map_of_mem _ j.property⟩=(1 : D) ⊗ₜ[K] j := by
  let f := FourCorner.FlatIdealTensorEquiv.idealTensorEquiv (S:=B) J
  have hf : f ((1 : B) ⊗ₜ[A] j)=⟨algebraMap A B (j : A),Ideal.mem_map_of_mem _ j.property⟩ := by
    apply Subtype.ext
    change FourCorner.FlatIdealTensorEquiv.idealTensorMap J ((1 : B) ⊗ₜ[A] j)=algebraMap A B (j : A)
    simpa only [mul_one] using FourCorner.FlatIdealTensorEquiv.idealTensorMap_tmul J (1 : B) j
  change sourceCoordinates K A D B J e (f.symm ⟨algebraMap A B (j : A),Ideal.mem_map_of_mem _ j.property⟩)=_
  rw [← hf,LinearEquiv.symm_apply_apply,sourceCoordinates_one_tmul]

#print axioms idealCoordinates
#print axioms idealCoordinates_source
end
end FourCorner.RelativeTensorCancel
