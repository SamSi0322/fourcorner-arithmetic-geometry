import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Prod

noncomputable section
open Polynomial LaurentPolynomial

namespace FourCorner.StandardLaurentCech
variable {R : Type*} [CommRing R]

/-- Sections on the U chart, where the coordinate is T. -/
def plus : Polynomial R →ₗ[R] LaurentPolynomial R :=
  Polynomial.toLaurentAlg.toLinearMap

/-- Sections on the V chart, where the coordinate is T inverse, with
the literal transition factor T^d. -/
def minus (d : ℤ) : Polynomial R →ₗ[R] LaurentPolynomial R :=
  (LinearMap.mulLeft R (T d)).comp
    (LaurentPolynomial.invert.toLinearMap.comp plus)

/-- The ordered (V,U) differential is -restriction(V)+restriction(U). -/
def differential (d : ℤ) : Polynomial R × Polynomial R →ₗ[R] LaurentPolynomial R :=
  (-(minus (R := R) d)).coprod (plus (R := R))

theorem plus_apply (p : Polynomial R) : plus p = p.toLaurent := rfl

theorem minus_apply (d : ℤ) (p : Polynomial R) :
    minus d p = T d * LaurentPolynomial.invert p.toLaurent := rfl

theorem differential_apply (d : ℤ) (p q : Polynomial R) :
    differential d (p,q) = -(minus d p) + plus q := rfl

theorem plus_injective : Function.Injective (plus (R := R)) :=
  Polynomial.toLaurent_injective

theorem minus_injective (d : ℤ) : Function.Injective (minus (R := R) d) := by
  intro p q h
  apply plus_injective
  apply LaurentPolynomial.invert.injective
  have hh := congrArg (fun z : LaurentPolynomial R => T (-d) * z) h
  simpa only [plus_apply, minus_apply, ← mul_assoc, ← T_add, neg_add_cancel, T_zero, one_mul] using hh

theorem plus_monomial (n : ℕ) (a : R) :
    plus (monomial n a) = LaurentPolynomial.C a * T (n : ℤ) :=
  Polynomial.toLaurent_C_mul_T n a

theorem minus_monomial (d : ℤ) (n : ℕ) (a : R) :
    minus d (monomial n a) = LaurentPolynomial.C a * T (d - n) := by
  rw [minus_apply, Polynomial.toLaurent_C_mul_T, map_mul,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  rw [← mul_assoc, mul_comm (T d) (LaurentPolynomial.C a), mul_assoc,
    ← T_add, ← sub_eq_add_neg]

#print axioms plus_injective
#print axioms minus_injective
#print axioms plus_monomial
#print axioms minus_monomial
end FourCorner.StandardLaurentCech
