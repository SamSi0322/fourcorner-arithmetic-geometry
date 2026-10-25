import FourCorner.CommonRootPadicVal
import Mathlib.Tactic

namespace FourCorner

/-- A normalized integral four-distance configuration over the actual dyadic field.
The scale and every root remain explicit, and the four quadrics are imposed together. -/
structure CommonDyadicFrame (t : ℚ_[2]) where
  N : ℚ_[2]
  X : ℚ_[2]
  Y : ℚ_[2]
  A0 : ℚ_[2]
  A1 : ℚ_[2]
  A2 : ℚ_[2]
  A3 : ℚ_[2]
  h : ℕ
  h_ge_two : 2 ≤ h
  N_ne_zero : N ≠ 0
  valN : N.valuation = (h : ℤ)
  valA0 : A0.valuation = 0
  valA1 : A1.valuation = 0
  valA2 : A2.valuation = 0
  valA3 : A3.valuation = 0
  A0_ne_zero : A0 ≠ 0
  A1_ne_zero : A1 ≠ 0
  A2_ne_zero : A2 ≠ 0
  A3_ne_zero : A3 ≠ 0
  sq0 : A0^2 = X^2+Y^2
  sq1 : A1^2 = (N-X)^2+Y^2
  sq2 : A2^2 = X^2+(N-Y)^2
  sq3 : A3^2 = (N-X)^2+(N-Y)^2
  t_eq : t = (A0*A3+A1*A2)/N^2
  U_ne_zero : N-2*X ≠ 0
  valU : (N-2*X).valuation = 1
  V_case : N-2*Y = 0 ∨ 2 ≤ (N-2*Y).valuation

namespace CommonDyadicFrame

theorem product_identity {t : ℚ_[2]} (F : CommonDyadicFrame t) :
    (F.A0*F.A3+F.A1*F.A2)*(F.A0*F.A3-F.A1*F.A2) =
      -F.N^2*(F.N-2*F.X)*(F.N-2*F.Y) := by
  calc
    _ = F.A0^2*F.A3^2-F.A1^2*F.A2^2 := by ring
    _ = _ := by rw [F.sq0,F.sq1,F.sq2,F.sq3];ring

end CommonDyadicFrame
#print axioms CommonDyadicFrame.product_identity
end FourCorner
