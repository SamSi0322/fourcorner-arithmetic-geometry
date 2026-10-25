import FourCorner.CommonRootSource
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace FourCorner
namespace CommonRootSource

variable {K : Type*} [Field K] {t : K}

/-- The two centered return coordinates from the actual source roots. -/
def returnU (S : CommonRootSource K t) : K := (S.P*S.M-S.B*S.C)/2
def returnV (S : CommonRootSource K t) : K := (S.P*S.M+S.B*S.C)/2

/-- Coordinates of the four-square return, with the paper's fixed labels. -/
def returnX (S : CommonRootSource K t) : K := (1-S.returnU)/2
def returnY (S : CommonRootSource K t) : K := (1-S.returnV)/2
def returnR0 (S : CommonRootSource K t) : K := (S.P-S.M)/2
def returnR1 (S : CommonRootSource K t) : K := (S.B-S.C)/2
def returnR2 (S : CommonRootSource K t) : K := (S.B+S.C)/2
def returnR3 (S : CommonRootSource K t) : K := (S.P+S.M)/2

/-- The source equations force the diagonal square balance. -/
theorem return_square_balance (S : CommonRootSource K t) :
    S.P^2+S.M^2 = S.B^2+S.C^2 := by
  rw [S.sqP,S.sqM,S.sqB,S.sqC]
  field_simp [S.ell_ne_zero]
  ring

/-- The quartic identity needed by the coordinate return. -/
theorem return_square_product (S : CommonRootSource K t) :
    S.P^2*S.M^2+S.B^2*S.C^2 = 2*(S.P^2+S.M^2-2) := by
  rw [S.sqP,S.sqM,S.sqB,S.sqC]
  field_simp [S.ell_ne_zero]
  ring

/-- The difference of the two diagonal products recovers the source parameter. -/
theorem return_parameter_identity (S : CommonRootSource K t) :
    S.P^2-S.M^2+S.B^2-S.C^2 = 4*t := by
  rw [S.sqP,S.sqM,S.sqB,S.sqC]
  field_simp [S.ell_ne_zero]
  ring

variable [CharZero K]

/-- All four exact distance identities follow from the four source equations.
This is an algebraic return and imposes no real ordering or positivity. -/
theorem return_four_squares (S : CommonRootSource K t) :
    S.returnR0^2 = S.returnX^2+S.returnY^2 ∧
    S.returnR1^2 = (1-S.returnX)^2+S.returnY^2 ∧
    S.returnR2^2 = S.returnX^2+(1-S.returnY)^2 ∧
    S.returnR3^2 = (1-S.returnX)^2+(1-S.returnY)^2 := by
  have hbalance := S.return_square_balance
  have hproduct := S.return_square_product
  unfold returnR0 returnR1 returnR2 returnR3 returnX returnY returnU returnV
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination -hproduct/8
  · linear_combination -hproduct/8-hbalance/4
  · linear_combination -hproduct/8-hbalance/4
  · linear_combination -hproduct/8

/-- The opposite-pair product sum is exactly the original parameter. -/
theorem return_opposite_product (S : CommonRootSource K t) :
    S.returnR0*S.returnR3+S.returnR1*S.returnR2 = t := by
  unfold returnR0 returnR3 returnR1 returnR2
  linear_combination S.return_parameter_identity/4

end CommonRootSource
end FourCorner
#print axioms FourCorner.CommonRootSource.return_four_squares
#print axioms FourCorner.CommonRootSource.return_opposite_product
