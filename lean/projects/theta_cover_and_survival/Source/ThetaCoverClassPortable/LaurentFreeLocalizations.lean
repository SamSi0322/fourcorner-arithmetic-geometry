import ThetaCoverClassPortable.LaurentFreeTwists
import ThetaCoverClassPortable.FiniteMapLaurentLocalizations
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial LaurentPolynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] {ι : Type*} [Finite ι]

theorem freeTwist_positive_localizes (d : ℤ) :
    PositiveLocalizes (freeTwistSections (R := R) (ι := ι) d) := by
  letI : Module R[X] (ι → LaurentPolynomial R) :=
    Module.compHom (ι → LaurentPolynomial R) (Polynomial.toLaurent : R[X] →+* LaurentPolynomial R)
  have h : IsLocalizedModule.Away (X : R[X])
      (LinearMap.pi fun i : ι => (Algebra.linearMap R[X] (LaurentPolynomial R)).comp (LinearMap.proj i)) :=
    inferInstance
  exact h

theorem freeTwist_negative_localizes (d : ℤ) :
    NegativeLocalizes (freeTwistSections (R := R) (ι := ι) d) := by
  letI : Algebra R[X] (LaurentPolynomial R) :=
    (FourCorner.StandardLaurentCech.negativeAlg (R := R)).toRingHom.toAlgebra
  letI : Module R[X] (LaurentPolynomial R) :=
    Module.compHom (LaurentPolynomial R) (FourCorner.StandardLaurentCech.negativeAlg (R := R)).toRingHom
  haveI : IsLocalization.Away (X : R[X]) (LaurentPolynomial R) :=
    FourCorner.StandardLaurentCech.negative_localization
  letI : Module R[X] (ι → LaurentPolynomial R) :=
    Module.compHom (ι → LaurentPolynomial R) (FourCorner.StandardLaurentCech.negativeAlg (R := R)).toRingHom
  let q : (ι → R[X]) →ₗ[R[X]] (ι → LaurentPolynomial R) :=
    LinearMap.pi fun i => (Algebra.linearMap R[X] (LaurentPolynomial R)).comp (LinearMap.proj i)
  haveI : IsLocalizedModule.Away (X : R[X]) q := inferInstance
  let E : (ι → LaurentPolynomial R) ≃ₗ[R[X]] (ι → LaurentPolynomial R) :=
    (LinearEquiv.smulOfUnit (R := LaurentPolynomial R) (M := ι → LaurentPolynomial R)
      (LaurentPolynomial.isUnit_T (R := R) d).unit).restrictScalars R[X]
  have hE (z : ι → LaurentPolynomial R) (i : ι) : E z i = T d * z i := by
    change ((LaurentPolynomial.isUnit_T (R := R) d).unit : LaurentPolynomial R) * z i = _
    rw [IsUnit.unit_spec]
  have h : IsLocalizedModule.Away (X : R[X]) (E.toLinearMap.comp q) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers (X : R[X])) q E
  let r : (ι → R[X]) →ₗ[R[X]] (ι → LaurentPolynomial R) :=
    negativeRestriction (freeTwistSections (R := R) (ι := ι) d)
  have he : r = E.toLinearMap.comp q := by
    apply LinearMap.ext
    intro p
    funext i
    change FourCorner.StandardLaurentCech.minus d (p i) = E (q p) i
    rw [hE]
    rfl
  change IsLocalizedModule.Away (X : R[X]) r
  rw [he]
  exact h
end FourCorner.FiniteMapCohomology
