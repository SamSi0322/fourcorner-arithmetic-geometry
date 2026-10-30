import ThetaCoverClassPortable.PairTargetLinearity

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

/-- The actual target-semilinear pre-coaction is K-linear, by the original
K-algebra target map. No coassociativity input is used. -/
def gammaK (t : A →ₐ[K] B) (gamma : M →+ B ⊗[A] M)
    (hgamma : ∀ a m, gamma (a • m) = t a • gamma m) : M →ₗ[K] B ⊗[A] M := by
  refine { toFun := gamma, map_add' := gamma.map_add, map_smul' := ?_ }
  intro k m
  calc
        gamma (k • m) = gamma (algebraMap K A k • m) :=
          congrArg gamma (IsScalarTower.algebraMap_smul (A := A) k m).symm
        _ = t (algebraMap K A k) • gamma m := hgamma _ _
        _ = k • gamma m := by
          rw [t.commutes]
          exact IsScalarTower.algebraMap_smul (A := B) k _

/-- Rho is genuinely constructed by beta after gamma. -/
def rhoK (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (gamma : M →+ B ⊗[A] M) (hgamma : ∀ a m, gamma (a • m) = t a • gamma m) :
    M →ₗ[K] D ⊗[K] M :=
  (sourceCoordinates K A D B M e).toLinearMap.comp (gammaK K A B M t gamma hgamma)

 theorem rhoK_A_smul (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, e ((1 : D) ⊗ₜ[A] t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (gamma : M →+ B ⊗[A] M) (hgamma : ∀ a m, gamma (a • m) = t a • gamma m)
    (a : A) (m : M) :
    rhoK K A D B M e t gamma hgamma (a • m) =
      algebraMap A D a • rhoK K A D B M e t gamma hgamma m := by
  change sourceCoordinates K A D B M e (gamma (a • m)) =
    algebraMap A D a • sourceCoordinates K A D B M e (gamma m)
  rw [hgamma]
  exact sourceCoordinates_target_smul K A D B M e t ht a (gamma m)

/-- Surjectivity of the ACTUAL A->D upgrades the proved A-target linearity
to D-linearity, retaining the original K-linear rho map. -/
def rhoD (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, e ((1 : D) ⊗ₜ[A] t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (gamma : M →+ B ⊗[A] M) (hgamma : ∀ a m, gamma (a • m) = t a • gamma m)
    (ho : Function.Surjective (algebraMap A D)) : M →ₗ[D] D ⊗[K] M :=
  { (rhoK K A D B M e t gamma hgamma).toAddMonoidHom with
    map_smul' := by
      intro d m
      obtain ⟨a, rfl⟩ := ho d
      rw [IsScalarTower.algebraMap_smul (A := D)]
      exact rhoK_A_smul K A D B M e t ht gamma hgamma a m }

@[simp] theorem rhoD_apply (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, e ((1 : D) ⊗ₜ[A] t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (gamma : M →+ B ⊗[A] M) (hgamma : ∀ a m, gamma (a • m) = t a • gamma m)
    (ho : Function.Surjective (algebraMap A D)) (m : M) :
    rhoD K A D B M e t ht gamma hgamma ho m =
      sourceCoordinates K A D B M e (gamma m) := rfl

end FourCorner.PairCoactionTransfer
