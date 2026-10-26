import HasseUnitFifteenNormalization

namespace FourCorner.HasseUnitFifteenFactor

open HasseUnitFifteenNormalization

noncomputable def coefficient (p Z U w T : ℚ_[2]) : ℚ_[2] :=
  -p*((p-1)*(p*(p+1)*(w+2*T+2*Z))*U-
    p*(-(p+1)*((p-1)*w+2*p*T+2*(p-1)*Z))*T+
    p*(p+1)*((p-1)*w-2*(p+1)*Z)*Z)

/-- Exact factor of the original tangent coefficient in the unit-fifteen
source gauge; the sole algebraic input is the original conic equation. -/
theorem coefficient_factor (p Z s x y z : ℚ_[2])
    (hp : p= -1+2*s^2) (hx : (1-s^2)*x^2=(1-2*s^2)*(2*z^2-1)) :
    coefficient p Z (s*x*Z) (2*s*y*Z) (2*s*z*Z)=
      8*p^2*s^3*(1-s^2)*Z^2*numerator s x y z := by
  dsimp [coefficient,numerator]
  rw [hp]
  linear_combination -8*Z^2*s^4*(-1+2*s^2)^2*hx

#print axioms coefficient_factor

end FourCorner.HasseUnitFifteenFactor
