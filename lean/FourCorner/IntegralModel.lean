import FourCorner.RadiusModel
import Mathlib.Data.Int.GCD

namespace FourCorner

/-- The primitive integral form of the original four-distance problem.
All variables are actual integers; the four roots and strict inequalities
are retained. The coprimality is joint coprimality of the three coordinates. -/
structure IntegralModel where
  L : ℤ
  X : ℤ
  Y : ℤ
  A₀ : ℤ
  A₁ : ℤ
  A₂ : ℤ
  A₃ : ℤ
  L_pos : 0 < L
  X_pos : 0 < X
  X_lt : X < L
  Y_pos : 0 < Y
  Y_lt : Y < L
  A₀_pos : 0 < A₀
  A₁_pos : 0 < A₁
  A₂_pos : 0 < A₂
  A₃_pos : 0 < A₃
  primitive : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs = 1
  sq₀ : A₀ ^ 2 = X ^ 2 + Y ^ 2
  sq₁ : A₁ ^ 2 = (L - X) ^ 2 + Y ^ 2
  sq₂ : A₂ ^ 2 = X ^ 2 + (L - Y) ^ 2
  sq₃ : A₃ ^ 2 = (L - X) ^ 2 + (L - Y) ^ 2

end FourCorner
