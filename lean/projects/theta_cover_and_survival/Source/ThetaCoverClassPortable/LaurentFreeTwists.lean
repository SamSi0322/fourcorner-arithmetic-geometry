import ThetaCoverClassPortable.LaurentLocalizedSections
import ThetaCoverClassPortable.StandardLaurentFamilies
import ThetaCoverClassPortable.NegativeLaurentLocalization
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial LaurentPolynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] {ι : Type*}

/-- The literal finite free standard twist as actual two-chart Sections. -/
def freeTwistSections (d : ℤ) : TwoChartCech.Sections (laurentCover R) where
  M0 := ι → R[X]
  M1 := ι → R[X]
  M01 := ι → LaurentPolynomial R
  M0_moduleA := inferInstanceAs (Module R[X] (ι → R[X]))
  M1_moduleA := inferInstanceAs (Module R[X] (ι → R[X]))
  M01_moduleA := inferInstanceAs (Module (LaurentPolynomial R) (ι → LaurentPolynomial R))
  r0 := {
    toFun := fun p i => FourCorner.StandardLaurentCech.minus d (p i)
    map_add' := fun p q => funext fun i => (FourCorner.StandardLaurentCech.minus d).map_add _ _
    map_smul' := fun r p => funext fun i => (FourCorner.StandardLaurentCech.minus d).map_smul _ _ }
  r1 := {
    toFun := fun p i => FourCorner.StandardLaurentCech.plus (p i)
    map_add' := fun p q => funext fun i => FourCorner.StandardLaurentCech.plus.map_add _ _
    map_smul' := fun r p => funext fun i => FourCorner.StandardLaurentCech.plus.map_smul _ _ }
  r0_smul p x := by
    funext i
    change T d * LaurentPolynomial.invert (Polynomial.toLaurent (p*x i)) =
      LaurentPolynomial.invert (Polynomial.toLaurent p) * (T d * LaurentPolynomial.invert (Polynomial.toLaurent (x i)))
    rw [map_mul,map_mul]
    ring
  r1_smul p x := by
    funext i
    exact map_mul Polynomial.toLaurent p (x i)

 theorem freeTwist_differential (d : ℤ) :
    (freeTwistSections (R := R) (ι := ι) d).cechDiff = FourCorner.StandardLaurentCech.familyDiff d := by
  apply LinearMap.ext
  intro z
  funext i
  change (-(FourCorner.StandardLaurentCech.minus d (z.1 i)) + FourCorner.StandardLaurentCech.plus (z.2 i)) = _
  rfl

 theorem freeTwist_finite_H0 [Finite ι] (d : ℤ) :
    Module.Finite R (freeTwistSections (R := R) (ι := ι) d).H0 := by
  change Module.Finite R (LinearMap.ker (freeTwistSections (R := R) (ι := ι) d).cechDiff)
  rw [freeTwist_differential]
  exact FourCorner.StandardLaurentCech.finite_family_H0 d

 theorem freeTwist_finite_H1 [Finite ι] (d : ℤ) :
    Module.Finite R (freeTwistSections (R := R) (ι := ι) d).H1 := by
  change Module.Finite R ((ι → LaurentPolynomial R) ⧸ LinearMap.range (freeTwistSections (R := R) (ι := ι) d).cechDiff)
  rw [freeTwist_differential]
  exact FourCorner.StandardLaurentCech.finite_family_H1 d

end FourCorner.FiniteMapCohomology
