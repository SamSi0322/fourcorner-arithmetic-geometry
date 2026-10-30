import ThetaCoverClassPortable.TripleModuleCoordinates
import ThetaCoverClassPortable.IdealCoringCocycle

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.PairCoactionTransfer
open FourCorner.RelativeTensorCancel FourCorner.StableIdealTransport
universe u
variable (K A D B M : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]
variable [AddCommGroup M] [Module K M] [Module A M] [Module D M]
variable [IsScalarTower K A M] [IsScalarTower K D M] [IsScalarTower A D M]

@[instance_reducible] def oppositeAAlgebra (t : A →ₐ[K] B) :
    Algebra A (reversePoint K A B t) :=
  (oppositeSource (algebraMap A B) t.toRingHom).toAlgebra

@[instance_reducible] def oppositeKAlgebra (t : A →ₐ[K] B) :
    Algebra K (reversePoint K A B t) :=
  ((oppositeSource (algebraMap A B) t.toRingHom).comp (algebraMap K A)).toAlgebra

theorem oppositeKATower (t : A →ₐ[K] B) :
    letI := oppositeAAlgebra K A B t
    letI := oppositeKAlgebra K A B t
    IsScalarTower K A (reversePoint K A B t) := by
  letI := oppositeAAlgebra K A B t
  letI := oppositeKAlgebra K A B t
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The actual triple ring map preserves the source quotient action. -/
theorem tripleCoordinates_source_action (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D)
    (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a) :
    letI := oppositeAAlgebra K A B t
    ∀ a : A, tripleCoordinates K A D B e t ht (algebraMap A (reversePoint K A B t) a) =
      algebraMap A (tripleRing K D) a := by
  letI := oppositeAAlgebra K A B t
  intro a
  change tripleCoordinates K A D B e t ht
    ((FourCorner.RingMapTensorPushout.right (algebraMap A B) t.toRingHom).hom (algebraMap A B a)) = _
  rw [tripleCoordinates_right]
  change rightPair K D (pairMap K A D B e (algebraMap A B a)) = _
  rw [pairMap_source, rightPair_tmul]
  rw [IsScalarTower.algebraMap_apply A D (tripleRing K D)]
  rfl

/-- Actual module map out of reverse-composable source tensors. -/
def oppositeCoordinates (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D)
    (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a) :
    letI := oppositeAAlgebra K A B t
    letI := oppositeKAlgebra K A B t
    reversePoint K A B t ⊗[A] M →ₗ[K] D ⊗[K] (D ⊗[K] M) := by
  letI := oppositeAAlgebra K A B t
  letI := oppositeKAlgebra K A B t
  letI := oppositeKATower K A B t
  exact coefficientCoordinates K A D (reversePoint K A B t) M
    (tripleCoordinates K A D B e t ht) (tripleCoordinates_source_action K A D B e t ht)

 theorem oppositeCoordinates_tmul (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D)
    (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (b : reversePoint K A B t) (m : M) :
    letI := oppositeAAlgebra K A B t
    letI := oppositeKAlgebra K A B t
    oppositeCoordinates K A D B M e t ht (b ⊗ₜ[A] m) =
      tripleContract K D M (tripleCoordinates K A D B e t ht b ⊗ₜ[D] m) := by
  letI := oppositeAAlgebra K A B t
  letI := oppositeKAlgebra K A B t
  letI := oppositeKATower K A B t
  exact coefficientCoordinates_tmul K A D (reversePoint K A B t) M _ _ b m

end FourCorner.PairCoactionTransfer
