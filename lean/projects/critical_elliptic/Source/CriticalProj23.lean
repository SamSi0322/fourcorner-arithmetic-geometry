import Slot02ProjectiveQuotient
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-! Literal projective critical intersection of the paper, over every field. -/
noncomputable section
set_option autoImplicit false
namespace FourCorner.CriticalProj23
open MvPolynomial AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k]
abbrev Ambient (k : Type*) [CommRing k] := MvPolynomial (Fin 4) k

def F0 (i : k) : Ambient k := X 2 ^ 2 - X 0 ^ 2 - C i * (X 1 ^ 2 - X 0 ^ 2)
def F1 (i : k) : Ambient k := X 3 ^ 2 - X 0 ^ 2 - C (1+i) * (X 1 ^ 2 - X 0 ^ 2)
def equation (i : k) : Fin 2 → Ambient k
  | 0 => F0 i
  | 1 => F1 i

theorem equation_homogeneous (i : k) (j : Fin 2) : (equation i j).IsHomogeneous 2 := by
  fin_cases j
  · exact ((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).sub
      (((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).C_mul _)
  · exact ((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).sub
      (((isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)).C_mul _)

def criticalIdeal (i : k) : Ideal (Ambient k) := Ideal.span (Set.range (equation i))
theorem criticalIdeal_homogeneous (i : k) :
    (criticalIdeal i).IsHomogeneous (homogeneousSubmodule (Fin 4) k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨j,rfl⟩
  exact ⟨2, equation_homogeneous i j⟩
def homogeneousIdeal (i : k) : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k) :=
  ⟨criticalIdeal i, criticalIdeal_homogeneous i⟩

/-- C_i as the projective spectrum of its literal homogeneous coordinate ring. -/
def criticalCurve (i : k) : Scheme :=
  Proj (HomogeneousIdealQuotientGrading.quotGrading
    (homogeneousSubmodule (Fin 4) k) (homogeneousIdeal i).toIdeal)

/-- Its actual closed immersion into P³, using the standard graded polynomial ring. -/
def inclusion (i : k) : criticalCurve i ⟶ Proj (homogeneousSubmodule (Fin 4) k) :=
  ProjectiveQuotient.quotientMap (homogeneousSubmodule (Fin 4) k) (homogeneousIdeal i)

theorem inclusion_isClosedImmersion (i : k) : IsClosedImmersion (inclusion i) :=
  ProjectiveQuotient.quotientMap_isClosedImmersion _ _

#print axioms criticalCurve
#print axioms inclusion_isClosedImmersion
end FourCorner.CriticalProj23
