import CriticalProper23
import CriticalQuotientChart

/-! The independent projective closure of (1,x,x²,y) for y²=x³−x.
This target is defined by its own equations, without reference to C_i. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]
abbrev ambient := MvPolynomial (Fin 4) K

def conic : ambient K := X 0 * X 2 - X 1 ^ 2
def cubicClosure : ambient K := X 3 ^ 2 - X 1 * X 2 + X 0 * X 1
def equation : Fin 2 → ambient K
  | 0 => conic K
  | 1 => cubicClosure K

theorem homogeneous (j : Fin 2) : (equation K j).IsHomogeneous 2 := by
  fin_cases j
  · exact ((isHomogeneous_X K 0).mul (isHomogeneous_X K 2)).sub (isHomogeneous_X_pow 1 2)
  · exact ((isHomogeneous_X_pow 3 2).sub
      ((isHomogeneous_X K 1).mul (isHomogeneous_X K 2))).add
      ((isHomogeneous_X K 0).mul (isHomogeneous_X K 1))

abbrev ideal := CriticalQuotientChart.homogeneousIdeal (equation K) (homogeneous K)
def curve : Scheme := Proj (CriticalQuotientChart.G (equation K) (homogeneous K))
def inclusion : curve K ⟶ Proj (homogeneousSubmodule (Fin 4) K) :=
  ProjectiveQuotient.quotientMap (homogeneousSubmodule (Fin 4) K) (ideal K)
theorem closed_inclusion : IsClosedImmersion (inclusion K) :=
  ProjectiveQuotient.quotientMap_isClosedImmersion _ _
def toBase : curve K ⟶ Spec (.of K) :=
  inclusion K ≫ CriticalProj23.ambientToSpec
theorem proper : IsProper (toBase K) := by
  haveI := closed_inclusion K
  haveI : IsProper (CriticalProj23.ambientToSpec (k := K)) :=
    CriticalProj23.ambientToSpec_isProper
  unfold toBase
  infer_instance

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.proper
