import ThetaCoverClassPortable.StandardLaurentCech
import Mathlib.RingTheory.Localization.Basic

noncomputable section
open Polynomial LaurentPolynomial
namespace FourCorner.StandardLaurentCech
variable {R : Type*} [CommRing R]

/-- The actual inverse-coordinate polynomial algebra map. -/
def negativeAlg : Polynomial R →ₐ[R] LaurentPolynomial R :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

theorem negativeAlg_apply (p : Polynomial R) :
    negativeAlg p = LaurentPolynomial.invert p.toLaurent := rfl

theorem minus_eq_shift_negative (d : ℤ) (p : Polynomial R) :
    minus d p = T d * negativeAlg p := rfl

@[simp] theorem negativeAlg_X : negativeAlg (R := R) X = T (-1) := by
  rw [negativeAlg_apply, Polynomial.toLaurent_X, LaurentPolynomial.invert_T]

theorem negative_localization :
    letI : Algebra (Polynomial R) (LaurentPolynomial R) := (negativeAlg (R := R)).toRingHom.toAlgebra
    IsLocalization.Away (X : Polynomial R) (LaurentPolynomial R) := by
  exact (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers (X : Polynomial R))
    (LaurentPolynomial.invert (R := R)).toRingEquiv).mp
      (LaurentPolynomial.isLocalization (R := R))

#print axioms negativeAlg_X
#print axioms negative_localization
end FourCorner.StandardLaurentCech
