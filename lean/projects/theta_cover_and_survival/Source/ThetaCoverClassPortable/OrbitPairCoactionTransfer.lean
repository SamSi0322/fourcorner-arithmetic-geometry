import ThetaCoverClassPortable.PairCoactionTransport
import ThetaCoverClassPortable.OrbitIdealCoaction
import ThetaCoverClassPortable.IdealCoringCocycle
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.FiniteRelationOrbit
open FourCorner.FiniteRelationQuotient FourCorner.StableIdealTransport
open FourCorner.RelativeTensorCancel FourCorner.PairCoactionTransfer
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B]

/-- Coassociativity of the ACTUAL previously constructed original ideal-layer
rho. The original coring cocycle is proved upstream and transported through
actual triple coordinates and relative cancellation. NO coassociativity,
pair-coaction, coordinate compatibility, invariant, or descent premise is added. -/
theorem orbitIdealRho_pair_coassoc
    (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range = ⊤)
    (heq : ∀ T : Type u, ∀ [CommRing T], Equivalence (Related s.toRingHom t.toRingHom (T := T)))
    (hs : letI := s.toRingHom.toAlgebra; Module.Flat A B)
    (htflat : letI := t.toRingHom.toAlgebra; Module.Flat A B)
    (J : Ideal A) (hkill : RingHom.ker (orbitTargetHom s t x) * J = ⊥)
    (hstable : Ideal.map s.toRingHom J = Ideal.map t.toRingHom J) (j : J) :
    letI := orbitAlgebra s x
    TensorProduct.map (LinearMap.id : orbit s x →ₗ[K] orbit s x)
        (orbitIdealRho s t x hgen heq hs J hkill hstable)
        (orbitIdealRho s t x hgen heq hs J hkill hstable j) =
      TensorProduct.map (LinearMap.id : orbit s x →ₗ[K] orbit s x)
        (TensorProduct.mk K (orbit s x) J (1 : orbit s x))
        (orbitIdealRho s t x hgen heq hs J hkill hstable j) := by
  let D := orbit s x
  letI := orbitAlgebra s x
  letI := s.toRingHom.toAlgebra
  letI := (orbitTargetHom s t x).toAlgebra
  letI : IsScalarTower K A B :=
    IsScalarTower.of_algebraMap_eq (fun k => (s.commutes k).symm)
  letI : IsScalarTower K A D :=
    IsScalarTower.of_algebraMap_eq (fun k => ((orbitTarget s t x).commutes k).symm)
  letI := FourCorner.ModuleSurjectiveScalars.idealLayerModule (orbitTargetHom s t x)
    (orbitTarget_surjective s t x hgen) J hkill
  letI : IsScalarTower A D J :=
    FourCorner.ModuleSurjectiveScalars.idealLayerModule_tower (orbitTargetHom s t x)
      (orbitTarget_surjective s t x hgen) J hkill
  letI : IsScalarTower K D J :=
    FourCorner.ModuleSurjectiveScalars.idealLayerModule_base_tower (orbitTarget s t x)
      (orbitTarget_surjective s t x hgen) J hkill
  let e := orbitTensorPairEquiv s t x hgen heq
  let gamma := preGamma s.toRingHom t.toRingHom hs J hstable
  have heTarget (a : A) : pairMap K A D B e (t a) =
      (1 : D) ⊗ₜ[K] algebraMap A D a :=
    orbitTensorPair_target s t x hgen heq a
  have hgamma (a : A) (m : J) : gamma (a • m) = t a • gamma m :=
    preGamma_target_smul s.toRingHom t.toRingHom hs J hstable a m
  letI := oppositeAAlgebra K A B t
  letI := oppositeKAlgebra K A B t
  letI := oppositeKATower K A B t
  let cDelta := coringDelta s.toRingHom t.toRingHom hgen heq hs J
  let cIter := coringIterate s.toRingHom t.toRingHom hs htflat J hstable
  have hPull (z : B ⊗[A] J) : rightCoefficientMap K A B J t z =
      tensorMap s.toRingHom (oppositeRight s.toRingHom t.toRingHom) J z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul b m => rfl
  have hdelta (b : B) (m : J) : cDelta (b ⊗ₜ[A] m) =
      oppositeComposite s.toRingHom t.toRingHom hgen heq b ⊗ₜ[A] m :=
    coringDelta_tmul s.toRingHom t.toRingHom hgen heq hs J b m
  have hiter (b : B) (m : J) : cIter (b ⊗ₜ[A] m) =
      oppositeLeft s.toRingHom t.toRingHom b • rightCoefficientMap K A B J t (gamma m) := by
    rw [hPull]
    exact coringIterate_tmul s.toRingHom t.toRingHom hs htflat J hstable b m
  have hcoring (m : J) : cDelta (gamma m) = cIter (gamma m) :=
    preGamma_coring_cocycle s.toRingHom t.toRingHom hgen heq hs htflat J hstable m
  have hrho : rhoK K A D B J e t gamma hgamma =
      orbitIdealRho s t x hgen heq hs J hkill hstable := by
    ext m
    rfl
  have h := pair_coassoc_of_coring K A D B J e t heTarget
    (orbitTarget_surjective s t x hgen) hgen heq gamma hgamma
    cDelta cIter hdelta hiter hcoring j
  rw [hrho] at h
  exact h

end FourCorner.FiniteRelationOrbit
