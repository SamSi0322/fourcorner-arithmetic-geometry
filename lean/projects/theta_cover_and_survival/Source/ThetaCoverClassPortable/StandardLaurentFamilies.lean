import ThetaCoverClassPortable.StandardLaurentH0
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Polynomial LaurentPolynomial
namespace FourCorner.StandardLaurentCech
variable {R ι : Type*} [CommRing R]

def familyDiff (d : ℤ) : (ι → Polynomial R) × (ι → Polynomial R) →ₗ[R]
    (ι → LaurentPolynomial R) where
  toFun x i := differential d (x.1 i,x.2 i)
  map_add' x y := by
    funext i
    exact (differential (R := R) d).map_add (x.1 i,x.2 i) (y.1 i,y.2 i)
  map_smul' a x := by
    funext i
    exact (differential (R := R) d).map_smul a (x.1 i,x.2 i)

abbrev FamilyH0 (d : ℤ) := LinearMap.ker (familyDiff (R := R) (ι := ι) d)
abbrev FamilyH1 (d : ℤ) := (ι → LaurentPolynomial R) ⧸
  LinearMap.range (familyDiff (R := R) (ι := ι) d)

def familyH0Equiv (d : ℤ) : FamilyH0 (R := R) (ι := ι) d ≃ₗ[R] (ι → H0 (R := R) d) where
  toFun x i := ⟨(x.1.1 i,x.1.2 i), congrFun x.property i⟩
  invFun y := ⟨((fun i => (y i).1.1),(fun i => (y i).1.2)), funext fun i => (y i).property⟩
  left_inv x := by rfl
  right_inv y := by rfl
  map_add' x y := by rfl
  map_smul' a x := by rfl

def familyQuotient (d : ℤ) : (ι → LaurentPolynomial R) →ₗ[R] (ι → H1 (R := R) d) where
  toFun x i := (LinearMap.range (differential d)).mkQ (x i)
  map_add' x y := by
    apply funext; intro i
    exact (LinearMap.range (differential (R := R) d)).mkQ.map_add _ _
  map_smul' a x := by
    apply funext; intro i
    exact (LinearMap.range (differential (R := R) d)).mkQ.map_smul _ _

theorem familyQuotient_surjective (d : ℤ) :
    Function.Surjective (familyQuotient (R := R) (ι := ι) d) := by
  intro y
  choose z hz using fun i => Submodule.mkQ_surjective (LinearMap.range (differential d)) (y i)
  exact ⟨z, funext hz⟩

theorem familyQuotient_kernel (d : ℤ) :
    LinearMap.ker (familyQuotient (R := R) (ι := ι) d) = LinearMap.range (familyDiff d) := by
  classical
  ext x
  constructor
  · intro h
    have hx : ∀ i, x i ∈ LinearMap.range (differential (R := R) d) := by
      intro i
      exact (Submodule.Quotient.mk_eq_zero _).mp (congrFun h i)
    choose z hz using hx
    exact ⟨((fun i => (z i).1),(fun i => (z i).2)), funext hz⟩
  · rintro ⟨z, rfl⟩
    ext i
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(z.1 i,z.2 i), rfl⟩

def familyH1Equiv (d : ℤ) : FamilyH1 (R := R) (ι := ι) d ≃ₗ[R] (ι → H1 (R := R) d) :=
  (Submodule.quotEquivOfEq _ _ (familyQuotient_kernel d).symm).trans
    ((familyQuotient (R := R) (ι := ι) d).quotKerEquivOfSurjective
      (familyQuotient_surjective (R := R) (ι := ι) d))

theorem finite_family_H0 [Finite ι] (d : ℤ) : Module.Finite R (FamilyH0 (R := R) (ι := ι) d) := by
  haveI := finite_H0 (R := R) d
  exact Module.Finite.of_surjective (familyH0Equiv d).symm.toLinearMap (familyH0Equiv d).symm.surjective

theorem finite_family_H1 [Finite ι] (d : ℤ) : Module.Finite R (FamilyH1 (R := R) (ι := ι) d) := by
  haveI := finite_H1 (R := R) d
  exact Module.Finite.of_surjective (familyH1Equiv d).symm.toLinearMap (familyH1Equiv d).symm.surjective

#print axioms familyH0Equiv
#print axioms familyH1Equiv
#print axioms finite_family_H0
#print axioms finite_family_H1
end FourCorner.StandardLaurentCech
