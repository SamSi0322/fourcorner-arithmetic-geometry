import ModuleConstantRankPresentation
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.LinearAlgebra.TensorProduct.Pi
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
universe u
namespace FourCorner.ModuleLocalizedRank
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]

/-- A real localized equivalence remains an equivalence after any scalar extension
where the element being inverted is already a unit. -/
def tensorEquivOfLocalizedEquiv (h : A) (hu : IsUnit (algebraMap A B h))
    (e : LocalizedModule (Submonoid.powers h) M ≃ₗ[A]
      LocalizedModule (Submonoid.powers h) N) : B ⊗[A] M ≃ₗ[A] B ⊗[A] N := by
  let Ah := Localization.Away h
  have huall : ∀ y : Submonoid.powers h, IsUnit (algebraMap A B y) := by
    intro y
    obtain ⟨n, hn⟩ := y.2
    rw [← hn, map_pow]
    exact hu.pow n
  letI : Algebra Ah B := (IsLocalization.lift (S := Ah) huall).toAlgebra
  haveI : IsScalarTower A Ah B := IsScalarTower.of_algebraMap_eq (by
    intro a
    exact (IsLocalization.lift_eq (M := Submonoid.powers h) (S := Ah) huall a).symm)
  let E (P : Type u) [AddCommGroup P] [Module A P] :
      B ⊗[A] LocalizedModule (Submonoid.powers h) P ≃ₗ[A] B ⊗[A] P :=
    ((IsLocalization.moduleTensorEquiv (Submonoid.powers h) Ah B
        (LocalizedModule (Submonoid.powers h) P)).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl Ah B)
        (LocalizedModule.equivTensorProduct (Submonoid.powers h) P) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange A Ah Ah B P).restrictScalars A
  exact (E M).symm ≪≫ₗ TensorProduct.congr (LinearEquiv.refl A B) e ≪≫ₗ E N

/-- Tensoring the genuine Artinian ring decomposition gives the decomposition
of any module, without assuming that module is projective or free. -/
def tensorPiLocalization (D : Type u) [CommRing D] [IsArtinianRing D]
    [Algebra A D] (P : Type u) [AddCommGroup P] [Module A P] :
    D ⊗[A] P ≃ₗ[D] (∀ q : PrimeSpectrum D, Localization.AtPrime q.asIdeal ⊗[A] P) := by
  classical
  letI := Fintype.ofFinite (PrimeSpectrum D)
  exact (TensorProduct.lid D (D ⊗[A] P)).symm ≪≫ₗ
    TensorProduct.congr (PrimeSpectrum.toPiLocalizationEquiv D).toLinearEquiv
      (LinearEquiv.refl D (D ⊗[A] P)) ≪≫ₗ
    TensorProduct.piLeft D (D ⊗[A] P) (fun q : PrimeSpectrum D => Localization.AtPrime q.asIdeal) ≪≫ₗ
    LinearEquiv.piCongrRight (fun q =>
      TensorProduct.AlgebraTensorModule.cancelBaseChange A D D (Localization.AtPrime q.asIdeal) P)

section ScalarTensor
variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K] [Algebra R A]
  [Module R M] [IsScalarTower R A M]

/-- The actual two scalar-extension tensor presentations are R-linearly equivalent. -/
def scalarTensorEquiv :
    letI : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    (K ⊗[R] A) ⊗[A] M ≃ₗ[R] K ⊗[R] M := by
  letI : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let e : K ⊗[R] A ≃ₐ[A] A ⊗[R] K :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R K A).toRingEquiv) (fun a => by
      change (Algebra.TensorProduct.comm R K A) (1 ⊗ₜ[R] a) = a ⊗ₜ[R] 1
      rw [Algebra.TensorProduct.comm_tmul])
  exact ((TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)) ≪≫ₗ
    TensorProduct.comm A (A ⊗[R] K) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M K).restrictScalars R ≪≫ₗ
    TensorProduct.comm R M K
end ScalarTensor

section Rank
variable {R : Type u} [CommRing R] [Algebra R A] [Module.Finite R A]
  [Module R M] [Module R N] [IsScalarTower R A M] [IsScalarTower R A N]
  [Module.Finite R M] [Module.Finite R N] [Module.Flat R M] [Module.Flat R N]

/-- Compare actual residue fibres through the finite Artinian algebra, retaining
all module structures of the caller. -/
theorem rankAtMaximal_eq_of_localizedEquiv (s : Set A) (hs : Ideal.span s = ⊤)
    (he : ∀ h ∈ s, Nonempty (LocalizedModule (Submonoid.powers h) M ≃ₗ[A]
      LocalizedModule (Submonoid.powers h) N))
    (p : Ideal R) [p.IsMaximal] :
    Module.rankAtStalk M ⟨p, inferInstance⟩ = Module.rankAtStalk N ⟨p, inferInstance⟩ := by
  classical
  let K := p.ResidueField
  let D := K ⊗[R] A
  letI : Algebra A D := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Finite K D := inferInstance
  haveI : IsArtinianRing D := isArtinian_of_tower K inferInstance
  letI (q : PrimeSpectrum D) : Algebra A (Localization.AtPrime q.asIdeal) :=
    Algebra.ofModule smul_mul_assoc mul_smul_comm
  have hlocal (q : PrimeSpectrum D) : Nonempty
      (Localization.AtPrime q.asIdeal ⊗[A] M ≃ₗ[A] Localization.AtPrime q.asIdeal ⊗[A] N) := by
    have hn : ¬ s ⊆ (q.comap (algebraMap A D)).asIdeal := by
      intro hin
      exact (q.comap (algebraMap A D)).isPrime.ne_top (by
        have hz := Ideal.span_le.mpr hin
        rw [hs] at hz
        exact top_le_iff.mp hz)
    obtain ⟨h, hhs, hnot⟩ := Set.not_subset.mp hn
    have hu : IsUnit (algebraMap A (Localization.AtPrime q.asIdeal) h) := by
      have hmap : algebraMap A (Localization.AtPrime q.asIdeal) h =
          algebraMap D (Localization.AtPrime q.asIdeal) (algebraMap A D h) := by
        change h • (1 : Localization.AtPrime q.asIdeal) = _
        rw [← IsScalarTower.algebraMap_smul D h (1 : Localization.AtPrime q.asIdeal),
          Algebra.smul_def, mul_one]
      rw [hmap]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q.asIdeal) q.asIdeal _).mpr hnot
    exact ⟨tensorEquivOfLocalizedEquiv h hu (Classical.choice (he h hhs))⟩
  let E0 : D ⊗[A] M ≃ₗ[A] D ⊗[A] N :=
    (tensorPiLocalization D M).restrictScalars A ≪≫ₗ
    LinearEquiv.piCongrRight (fun q => Classical.choice (hlocal q)) ≪≫ₗ
    (tensorPiLocalization D N).symm.restrictScalars A
  let E : (K ⊗[R] M) ≃ₗ[R] K ⊗[R] N :=
    (scalarTensorEquiv (R := R) (K := K) (A := A) (M := M)).symm ≪≫ₗ
    E0.restrictScalars R ≪≫ₗ scalarTensorEquiv (R := R) (K := K) (A := A) (M := N)
  let EK := E.extendScalarsOfSurjective (p.algebraMap_residueField_surjective)
  rw [Module.rankAtStalk_eq, Module.rankAtStalk_eq]
  exact EK.finrank_eq
end Rank
end FourCorner.ModuleLocalizedRank

namespace Module
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
  (M N : Type u) [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module A M] [Module A N]
  [IsScalarTower R A M] [IsScalarTower R A N]
  [Module.Finite R M] [Module.Finite R N] [Module.Flat R M] [Module.Flat R N]

/-- The exact localized-module comparison used by the universal-divisor callers. -/
theorem rankAtStalk_eq_of_forall_localizedModule_equiv (s : Set A) (hs : Ideal.span s = ⊤)
    (he : ∀ h ∈ s, Nonempty (LocalizedModule (Submonoid.powers h) M ≃ₗ[A]
      LocalizedModule (Submonoid.powers h) N)) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk (R := R) N := by
  funext p
  obtain ⟨q, hq, hpq⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  letI := hq
  exact (Module.rankAtStalk_eq_of_le_of_finite_of_flat M hpq).trans
    ((FourCorner.ModuleLocalizedRank.rankAtMaximal_eq_of_localizedEquiv s hs he q).trans
      (Module.rankAtStalk_eq_of_le_of_finite_of_flat N hpq).symm)
end Module

