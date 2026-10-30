import ThetaCoverClassPortable.OppositeModuleCoordinates
import Mathlib.Algebra.Algebra.RestrictScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- Scalar-tagged copy of the SAME actual tensor module. The alias only
fixes its TARGET A-action through the left D; its K/D structures are original. -/
abbrev targetPair := RestrictScalars A D (D ⊗[K] M)

@[instance_reducible] def targetPairK : Module K (targetPair K A D M) :=
  inferInstanceAs (Module K (D ⊗[K] M))

@[instance_reducible] def targetPairD : Module D (targetPair K A D M) :=
  RestrictScalars.moduleOrig A D (D ⊗[K] M)

theorem targetPairKD :
    letI := targetPairK K A D M
    letI := targetPairD K A D M
    IsScalarTower K D (targetPair K A D M) := by
  letI := targetPairK K A D M
  letI := targetPairD K A D M
  exact inferInstanceAs (IsScalarTower K D (D ⊗[K] M))

theorem targetPairKA :
    letI := targetPairK K A D M
    letI := targetPairD K A D M
    IsScalarTower K A (targetPair K A D M) := by
  letI := targetPairK K A D M
  letI := targetPairD K A D M
  letI := targetPairKD K A D M
  apply IsScalarTower.of_algebraMap_smul
  intro k z
  change algebraMap A D (algebraMap K A k) • (z : D ⊗[K] M) = k • (z : D ⊗[K] M)
  rw [← IsScalarTower.algebraMap_apply K A D]
  exact IsScalarTower.algebraMap_smul (A := D) k z

/-- Literal right-arrow coefficient pull, for the same retained module M. -/
def rightCoefficientMap (t : A →ₐ[K] B) :
    letI := oppositeAAlgebra K A B t
    letI := oppositeKAlgebra K A B t
    B ⊗[A] M →ₗ[K] reversePoint K A B t ⊗[A] M := by
  letI := oppositeAAlgebra K A B t
  letI := oppositeKAlgebra K A B t
  letI := oppositeKATower K A B t
  let r : B →ₗ[A] reversePoint K A B t :=
    { toFun := oppositeRight (algebraMap A B) t.toRingHom
      map_add' := map_add _
      map_smul' := by
        intro a b
        change oppositeRight (algebraMap A B) t.toRingHom (a • b) =
          oppositeSource (algebraMap A B) t.toRingHom a *
            oppositeRight (algebraMap A B) t.toRingHom b
        rw [Algebra.smul_def, map_mul]
        rfl }
  exact (TensorProduct.map r (LinearMap.id : M →ₗ[A] M)).restrictScalars K

@[simp] theorem rightCoefficientMap_tmul (t : A →ₐ[K] B) (b : B) (m : M) :
    letI := oppositeAAlgebra K A B t
    letI := oppositeKAlgebra K A B t
    rightCoefficientMap K A B M t (b ⊗ₜ[A] m) =
      oppositeRight (algebraMap A B) t.toRingHom b ⊗ₜ[A] m := rfl

/-- The triple-coordinate map intertwines the actual reverse-composable
coefficient pull with TWO successive pair-source coordinate maps. -/
theorem oppositeCoordinates_left_right
    (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (b : B) (z : B ⊗[A] M) :
    letI := oppositeAAlgebra K A B t
    letI := oppositeKAlgebra K A B t
    letI := targetPairK K A D M
    letI := targetPairD K A D M
    letI := targetPairKD K A D M
    letI := targetPairKA K A D M
    oppositeCoordinates K A D B M e t ht
      (oppositeLeft (algebraMap A B) t.toRingHom b • rightCoefficientMap K A B M t z) =
      sourceCoordinates K A D B (targetPair K A D M) e
        (b ⊗ₜ[A] sourceCoordinates K A D B M e z) := by
  letI := oppositeAAlgebra K A B t
  letI := oppositeKAlgebra K A B t
  letI := oppositeKATower K A B t
  letI := targetPairK K A D M
  letI := targetPairD K A D M
  letI := targetPairKD K A D M
  letI := targetPairKA K A D M
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, smul_add, TensorProduct.tmul_add, hx, hy]
  | tmul b2 m =>
    rw [rightCoefficientMap_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      oppositeCoordinates_tmul, map_mul, tripleCoordinates_left, tripleCoordinates_right]
    simpa only [leftArrow, rightArrow, AlgHom.comp_apply, pairMap_apply,
      sourceCoordinates_tmul, targetPair, RestrictScalars, targetPairK, targetPairD, relativeCancel] using
      tripleContract_left_right K D M (pairMap K A D B e b) (pairMap K A D B e b2) m

end FourCorner.PairCoactionTransfer
