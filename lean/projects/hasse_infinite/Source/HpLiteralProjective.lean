import HpFamilyConstituents
import ThetaProjectiveModel
import ThetaModelBase

/-! The literal paper C_p as a projective homogeneous quotient, in the
original coordinate order [Z,U,V,W,T]. This file supplies actual equations,
charts, and the projective/proper structural maps. It does not assert a
scheme isomorphism with the canonical model without proving that bridge. -/
namespace FourCorner.HpLiteralProjective
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type*) [Field K]

abbrev ambient := MvPolynomial (Fin 5) K

def equation (p : K) : Fin 3 → ambient K
  | 0 => C p*(X 2)^2-C (2*(p-1))*((X 1)^2-C p*(X 0)^2)
  | 1 => C p*(X 3)^2-C (2*(p+1))*((X 1)^2+C p*(X 0)^2)
  | 2 => C p*(X 4)^2-C (p-1)*(X 1)^2-C (p*(p+1))*(X 0)^2

theorem homogeneous (p : K) (i : Fin 3) : (equation K p i).IsHomogeneous 2 := by
  fin_cases i
  · exact (isHomogeneous_C_mul_X_pow _ _ _).sub
      (((isHomogeneous_X_pow _ _).sub (isHomogeneous_C_mul_X_pow _ _ _)).C_mul _)
  · exact (isHomogeneous_C_mul_X_pow _ _ _).sub
      (((isHomogeneous_X_pow _ _).add (isHomogeneous_C_mul_X_pow _ _ _)).C_mul _)
  · exact ((isHomogeneous_C_mul_X_pow _ _ _).sub (isHomogeneous_C_mul_X_pow _ _ _)).sub
      (isHomogeneous_C_mul_X_pow _ _ _)

abbrev curve (p : K) := ThetaProjectiveModel.curve (equation K p) (homogeneous K p)
abbrev toBase (p : K) := ThetaProjectiveModel.toBase (equation K p) (homogeneous K p)
abbrev inclusion (p : K) := ThetaProjectiveModel.inclusion (equation K p) (homogeneous K p)
abbrev affineRing (p : K) (j : Fin 5) := ThetaProjectiveModel.affineRing (equation K p) j
abbrev chartIso (p : K) (j : Fin 5) := ThetaProjectiveModel.chartIso (equation K p) (homogeneous K p) j

theorem closed (p : K) : IsClosedImmersion (inclusion K p) := ThetaProjectiveModel.inclusion_closed _ _
theorem proper (p : K) : IsProper (toBase K p) := ThetaProjectiveModel.proper _ _

variable [CharZero K]

theorem homogeneous_equations (p : K) (x : Fin 5 → K) :
    (∀i,eval x (equation K p i)=0) ↔ CompleteSource11.Source p (x 0) (x 1) (x 2) (x 3) (x 4) := by
  simp only [CompleteSource11.Source]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [equation,map_add,map_sub,map_mul,map_pow,eval_C,eval_X] at h0 h1 h2
    exact ⟨sub_eq_zero.mp h0,sub_eq_zero.mp h1,by linear_combination h2⟩
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i <;> simp only [equation,map_add,map_sub,map_mul,map_pow,eval_C,eval_X]
    · linear_combination h0
    · linear_combination h1
    · linear_combination h2

#print axioms homogeneous
#print axioms closed
#print axioms proper
#print axioms homogeneous_equations
end
end FourCorner.HpLiteralProjective
