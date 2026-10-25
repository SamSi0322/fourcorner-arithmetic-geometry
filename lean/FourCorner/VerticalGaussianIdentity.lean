import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.LinearCombination

namespace FourCorner

/-- Algebraic identity for the Gaussian sum associated to a vertical unit segment. -/
theorem vertical_gaussian_identity (x y a b : ℚ)
    (ha : a ^ 2 = x ^ 2 + y ^ 2)
    (hb : b ^ 2 = x ^ 2 + (y + 1) ^ 2) :
    (b * x + a * x) ^ 2 - (b * y + a * (y + 1)) ^ 2 =
        ((a + b) ^ 2 - 1) * (x ^ 2 - y * (y + 1)) ∧
      2 * (b * x + a * x) * (b * y + a * (y + 1)) =
        ((a + b) ^ 2 - 1) * (x * (y + 1) + y * x) := by
  constructor
  · linear_combination -(y + 1) * ha + y * hb
  · linear_combination x * ha - x * hb

end FourCorner
