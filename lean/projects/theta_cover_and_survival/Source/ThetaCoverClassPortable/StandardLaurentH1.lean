import ThetaCoverClassPortable.StandardLaurentCech
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

noncomputable section
open Polynomial LaurentPolynomial
namespace FourCorner.StandardLaurentCech
variable {R : Type*} [CommRing R]

abbrev H1 (d : ℤ) := LaurentPolynomial R ⧸ LinearMap.range (differential (R := R) d)
abbrev Middle (d : ℤ) := AddMonoidAlgebra.supported R R (Set.Ioo d 0)

def middleToH1 (d : ℤ) : Middle (R := R) d →ₗ[R] H1 (R := R) d :=
  (LinearMap.range (differential d)).mkQ.comp (AddMonoidAlgebra.supported R R (Set.Ioo d 0)).subtype

theorem positive_monomial_in_range (d n : ℤ) (a : R) (hn : 0 ≤ n) :
    LaurentPolynomial.C a * T n ∈ LinearMap.range (differential (R := R) d) := by
  refine ⟨(0, monomial n.toNat a), ?_⟩
  simp only [differential_apply, map_zero, neg_zero, zero_add, plus_monomial,
    Int.toNat_of_nonneg hn]

theorem negative_monomial_in_range (d n : ℤ) (a : R) (hn : n ≤ d) :
    LaurentPolynomial.C a * T n ∈ LinearMap.range (differential (R := R) d) := by
  refine ⟨(-monomial (d-n).toNat a, 0), ?_⟩
  rw [differential_apply, map_neg, map_zero, neg_neg, add_zero, minus_monomial,
    Int.toNat_of_nonneg (sub_nonneg.mpr hn), sub_sub_cancel]

/-- Every cokernel class has a representative whose exponents lie strictly
between d and zero. No freeness, domain or Noetherian hypothesis is needed. -/
theorem middleToH1_surjective (d : ℤ) :
    Function.Surjective (middleToH1 (R := R) d) := by
  classical
  let q := (LinearMap.range (differential (R := R) d)).mkQ
  have lift_all (f : LaurentPolynomial R) : ∃ b, middleToH1 d b = q f := by
    induction f using LaurentPolynomial.induction_on' with
    | add f g hf hg =>
      obtain ⟨bf, hf⟩ := hf
      obtain ⟨bg, hg⟩ := hg
      exact ⟨bf+bg, by rw [map_add, hf, hg, map_add]⟩
    | C_mul_T n a =>
      by_cases hn : 0 ≤ n
      · refine ⟨0, ?_⟩
        rw [map_zero]
        symm
        exact (Submodule.Quotient.mk_eq_zero _).mpr (positive_monomial_in_range d n a hn)
      · by_cases hd : n ≤ d
        · refine ⟨0, ?_⟩
          rw [map_zero]
          symm
          exact (Submodule.Quotient.mk_eq_zero _).mpr (negative_monomial_in_range d n a hd)
        · have hs : LaurentPolynomial.C a * T n ∈ AddMonoidAlgebra.supported R R (Set.Ioo d 0) := by
            rw [AddMonoidAlgebra.mem_supported]
            intro k hk
            have heq : k = n := by simpa using (LaurentPolynomial.support_C_mul_T a n) hk
            subst k
            exact ⟨lt_of_not_ge hd, lt_of_not_ge hn⟩
          exact ⟨⟨_, hs⟩, rfl⟩
  intro z
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (differential (R := R) d)) z
  exact lift_all f

/-- Genuine finite cohomology of the literal standard Laurent two-chart complex. -/
theorem finite_H1 (d : ℤ) : Module.Finite R (H1 (R := R) d) := by
  classical
  haveI : Finite (Set.Ioo d (0 : ℤ)) := (Set.finite_Ioo d 0).to_subtype
  let e := AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) (Set.Ioo d 0)
  haveI : Module.Finite R (Middle (R := R) d) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_surjective (middleToH1 d) (middleToH1_surjective d)

#print axioms middleToH1_surjective
#print axioms finite_H1
end FourCorner.StandardLaurentCech
