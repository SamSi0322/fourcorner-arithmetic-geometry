import ThetaCoverClassPortable.DoubleCoordinateCompatibility
import ThetaCoverClassPortable.PairRhoLinearity
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.PairCoactionTransfer
open FourCorner.RelativeTensorCancel FourCorner.StableIdealTransport FourCorner.FiniteRelationQuotient
universe u
variable (K A D B M : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]
variable [AddCommGroup M] [Module K M] [Module A M] [Module D M]
variable [IsScalarTower K A M] [IsScalarTower K D M] [IsScalarTower A D M]

/-- Genuine coordinate transport of an original coring equality. The two
coefficient-pull formulas are stated in the ORIGINAL reverse composable ring,
and all triple-coordinate/naturality diagrams are PROVED above, not assumed. -/
theorem pair_coassoc_of_coring
    (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (ho : Function.Surjective (algebraMap A D))
    (hgen : (algebraMap A B).range ⊔ t.toRingHom.range = ⊤)
    (heq : ∀ T : Type u, ∀ [CommRing T], Equivalence (Related (algebraMap A B) t.toRingHom (T := T)))
    (gamma : M →+ B ⊗[A] M)
    (hgamma : ∀ a m, gamma (a • m) = t a • gamma m)
    (cDelta cIter : letI := oppositeAAlgebra K A B t
      (B ⊗[A] M) →+ (reversePoint K A B t ⊗[A] M))
    (hdelta : ∀ b m, letI := oppositeAAlgebra K A B t
      cDelta (b ⊗ₜ[A] m) = oppositeComposite (algebraMap A B) t.toRingHom hgen heq b ⊗ₜ[A] m)
    (hiter : ∀ b m, letI := oppositeAAlgebra K A B t
      letI := oppositeKAlgebra K A B t
      cIter (b ⊗ₜ[A] m) = oppositeLeft (algebraMap A B) t.toRingHom b •
        rightCoefficientMap K A B M t (gamma m))
    (hcoring : ∀ m, cDelta (gamma m) = cIter (gamma m)) (m : M) :
    TensorProduct.map (LinearMap.id : D →ₗ[K] D) (rhoK K A D B M e t gamma hgamma)
        (rhoK K A D B M e t gamma hgamma m) =
      TensorProduct.map (LinearMap.id : D →ₗ[K] D) (TensorProduct.mk K D M (1 : D))
        (rhoK K A D B M e t gamma hgamma m) := by
  letI := oppositeAAlgebra K A B t
  letI := oppositeKAlgebra K A B t
  letI := oppositeKATower K A B t
  let F := oppositeCoordinates K A D B M e t ht
  have hd (z : B ⊗[A] M) : F (cDelta z) =
      TensorProduct.map (LinearMap.id : D →ₗ[K] D) (TensorProduct.mk K D M (1 : D))
        (sourceCoordinates K A D B M e z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b j =>
      rw [hdelta, oppositeCoordinates_tmul]
      have h := RingHom.congr_fun
        (tripleCoordinates_delta K A D B e t ht hgen
          (oppositeComposite (algebraMap A B) t.toRingHom hgen heq)
          (oppositeComposite_source _ _ _ _) (oppositeComposite_target _ _ _ _)) b
      change tripleCoordinates K A D B e t ht
          (oppositeComposite (algebraMap A B) t.toRingHom hgen heq b) =
        directPair K D (pairMap K A D B e b) at h
      rw [h]
      simpa only [sourceCoordinates_tmul, pairMap_apply] using
        tripleContract_direct K D M (pairMap K A D B e b) j
  letI := targetPairK K A D M
  letI := targetPairD K A D M
  letI := targetPairKD K A D M
  letI := targetPairKA K A D M
  let f : M →ₗ[D] targetPair K A D M :=
    rhoD K A D B M e t ht gamma hgamma ho
  have hfK : (f.restrictScalars K : M →ₗ[K] D ⊗[K] M) = rhoK K A D B M e t gamma hgamma := by
    ext j
    rfl
  have hi0 (z : B ⊗[A] M) : F (cIter z) =
      sourceCoordinates K A D B (targetPair K A D M) e
        (TensorProduct.map (LinearMap.id : B →ₗ[A] B) (f.restrictScalars A) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b j =>
      rw [hiter, oppositeCoordinates_left_right, TensorProduct.map_tmul, LinearMap.id_apply]
      rfl
  have hi (z : B ⊗[A] M) : F (cIter z) =
      TensorProduct.map (LinearMap.id : D →ₗ[K] D) (rhoK K A D B M e t gamma hgamma)
        (sourceCoordinates K A D B M e z) := by
    rw [hi0, sourceCoordinates_natural K A D B M (targetPair K A D M) e f, hfK]
    rfl
  have h := congrArg (fun z => F z) (hcoring m)
  rw [hd, hi] at h
  exact h.symm

end FourCorner.PairCoactionTransfer
