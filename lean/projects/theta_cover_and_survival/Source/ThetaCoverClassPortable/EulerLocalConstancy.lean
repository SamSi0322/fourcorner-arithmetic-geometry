import ThetaCoverClassPortable.FiniteAugmentation
import ThetaCoverClassPortable.ScalarComparison
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.RankNullity

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
universe u
namespace FourCorner.EulerAugmentation

/-- Rank-nullity is used ONLY on the genuinely finite auxiliary complex. -/
theorem finite_complex_euler {K P Q : Type u} [Field K]
    [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    [Module.Finite K P] [Module.Finite K Q] (a : P →ₗ[K] Q) :
    (Module.finrank K (LinearMap.ker a) : ℤ) - Module.finrank K (Q ⧸ LinearMap.range a) =
      (Module.finrank K P : ℤ) - Module.finrank K Q := by
  have h0 := (LinearMap.ker a).finrank_quotient_add_finrank
  rw [a.quotKerEquivRange.finrank_eq] at h0
  have h1 := (LinearMap.range a).finrank_quotient_add_finrank
  have h0z := congrArg (fun n : ℕ => (n : ℤ)) h0
  have h1z := congrArg (fun n : ℕ => (n : ℤ)) h1
  simp only [Nat.cast_add] at h0z h1z
  omega

variable {R C0 C1 Q : Type u} [CommRing R]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup Q] [Module R Q]

def fibreEulerValue (d : C0 →ₗ[R] C1) (K : Type u) [Field K] [Algebra R K] : ℤ :=
  (Module.finrank K (LinearMap.ker (d.baseChange K)) : ℤ) -
    Module.finrank K ((K ⊗[R] C1) ⧸ LinearMap.range (d.baseChange K))

/-- Genuine cohomology comparisons, not a finite-dimensionality assumption
on either original chart, identify the actual Euler difference. -/
theorem fibreEuler_eq_auxiliary_rank_difference [IsNoetherianRing R] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) (ha : Function.Surjective (augment d f))
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R Q]
    (K : Type u) [Field K] [Algebra R K] :
    fibreEulerValue d K =
      (Module.finrank K (K ⊗[R] LinearMap.ker (augment d f)) : ℤ) -
        Module.finrank K (K ⊗[R] Q) := by
  haveI := finite_augmented_kernel d f
  haveI : Module.Finite K (K ⊗[R] LinearMap.ker (augment d f)) := inferInstance
  haveI : Module.Finite K (K ⊗[R] Q) := inferInstance
  have e0 := kernelBoundaryBaseChangeEquiv d f ha K
  have e1 := cokerBoundaryBaseChangeEquiv d f ha K
  unfold fibreEulerValue
  rw [←e0.finrank_eq,←e1.finrank_eq]
  exact finite_complex_euler ((boundary d f).baseChange K)

/-- Flat original terms and finite original cohomology genuinely construct
one global finite-projective two-term model; its actual ranks prove LC. -/
theorem isLocallyConstant_fibreEulerValue [IsNoetherianRing R]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    IsLocallyConstant (fun p : PrimeSpectrum R => fibreEulerValue d p.asIdeal.ResidueField) := by
  obtain ⟨n,f,ha⟩ := exists_surjective_augmentation d
  let Q := Fin n → R
  let P := LinearMap.ker (augment d f)
  haveI : Module.Finite R P := finite_augmented_kernel d f
  haveI : Module.Projective R P := projective_augmented_kernel d f ha
  haveI : Module.Flat R P := inferInstance
  haveI : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
  haveI : Module.FinitePresentation R Q := Module.finitePresentation_of_finite R Q
  have hP := Module.isLocallyConstant_rankAtStalk (R := R) (M := P)
  have hQ := Module.isLocallyConstant_rankAtStalk (R := R) (M := Q)
  have hloc : IsLocallyConstant (fun p : PrimeSpectrum R =>
      (Module.rankAtStalk P p : ℤ) - Module.rankAtStalk Q p) :=
    hP.comp₂ hQ (fun a b : ℕ => (a : ℤ)-b)
  have heq : (fun p : PrimeSpectrum R => fibreEulerValue d p.asIdeal.ResidueField) =
      (fun p : PrimeSpectrum R => (Module.rankAtStalk P p : ℤ) - Module.rankAtStalk Q p) := by
    funext p
    rw [Module.rankAtStalk_eq,Module.rankAtStalk_eq]
    exact fibreEuler_eq_auxiliary_rank_difference d f ha p.asIdeal.ResidueField
  rw [heq]
  exact hloc
end FourCorner.EulerAugmentation

namespace TwoChartCech
/-- Exact native missing caller leaf. The original C0,C1 are merely flat;
neither is assumed finite, free or projective. The actual kernel/cokernel
fibre difference is identified internally with finite-projective ranks. -/
theorem isLocallyConstant_fibreEulerChar
    {R C0 C1 : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    IsLocallyConstant (fun p : PrimeSpectrum R =>
      (Module.finrank p.asIdeal.ResidueField (LinearMap.ker (d.baseChange p.asIdeal.ResidueField)) : ℤ) -
        Module.finrank p.asIdeal.ResidueField
          ((p.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange p.asIdeal.ResidueField))) :=
  FourCorner.EulerAugmentation.isLocallyConstant_fibreEulerValue d
end TwoChartCech
