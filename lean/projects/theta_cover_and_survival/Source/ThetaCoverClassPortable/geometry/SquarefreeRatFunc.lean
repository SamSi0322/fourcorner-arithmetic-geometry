import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

open scoped BigOperators
open Polynomial

namespace FourCorner.CoverFields

/-- A square root in a fraction field of an integrally closed ring is integral
whenever its square belongs to that ring. Thus square testing does not acquire
new solutions by passing to the fraction field. -/
theorem isSquare_algebraMap_iff {R F : Type*} [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] [IsIntegrallyClosed R] (a : R) :
    IsSquare (algebraMap R F a) ↔ IsSquare a := by
  constructor
  · rintro ⟨b, hb⟩
    have hi : IsIntegral R b := by
      apply IsIntegral.of_pow (n := 2) (by decide)
      rw [pow_two, ← hb]
      exact isIntegral_algebraMap
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    refine ⟨c, IsFractionRing.injective R F ?_⟩
    simpa only [map_mul, hc] using hb
  · rintro ⟨b, rfl⟩
    exact ⟨algebraMap R F b, map_mul (algebraMap R F) b b⟩

/-- A genuine nonunit squarefree ring element is not square in its fraction
field. No ramification or field-degree conclusion is an input. -/
theorem squarefree_not_isSquare_fraction {R F : Type*} [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] [IsIntegrallyClosed R]
    (a : R) (hs : Squarefree a) (hu : ¬ IsUnit a) :
    ¬ IsSquare (algebraMap R F a) := by
  intro h
  obtain ⟨b, hb⟩ := (isSquare_algebraMap_iff (F := F) a).mp h
  have hbu : IsUnit b := hs b (hb ▸ dvd_rfl)
  exact hu (hb ▸ hbu.mul hbu)

/-- Pairwise coprime nonconstant squarefree polynomials give independent
square classes in the actual rational-function field: every nonempty product
is nonsquare. -/
theorem polynomial_prod_not_isSquare_ratFunc {K : Type*} [Field K]
    {ι : Type*} (s : Finset ι) (f : ι → K[X])
    (hne : s.Nonempty)
    (hrel : Set.Pairwise (s : Set ι) (fun i j => IsRelPrime (f i) (f j)))
    (hsq : ∀ i ∈ s, Squarefree (f i))
    (hunit : ∀ i ∈ s, ¬ IsUnit (f i)) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K) (∏ i ∈ s, f i)) := by
  apply squarefree_not_isSquare_fraction
  · exact Finset.squarefree_prod_of_pairwise_isCoprime hrel hsq
  · intro hu
    obtain ⟨i, hi⟩ := hne
    exact hunit i hi (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem f hi) hu)

#print axioms isSquare_algebraMap_iff
#print axioms squarefree_not_isSquare_fraction
#print axioms polynomial_prod_not_isSquare_ratFunc

end FourCorner.CoverFields
