import FourCorner.CommonRootMatrixLegendre
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum.LegendreSymbol

import Mathlib.Tactic
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace FourCorner

open scoped BigOperators Matrix

/-- The ordered six-prime support of the explicit obstruction family. -/
def commonSixPrimes : Fin 6 → ℕ := ![7, 17, 23, 31, 73, 311]

theorem commonSixPrimes_prime (i : Fin 6) : (commonSixPrimes i).Prime := by
  fin_cases i <;> norm_num [commonSixPrimes] <;> decide

theorem commonSixPrimes_injective : Function.Injective commonSixPrimes := by decide

theorem commonSixPrimes_mod_eight (i : Fin 6) :
    commonSixPrimes i % 8 = 1 ∨ commonSixPrimes i % 8 = 7 := by
  fin_cases i <;> norm_num [commonSixPrimes]

theorem commonSixPrimes_ne_two (i : Fin 6) : commonSixPrimes i ≠ 2 := by
  fin_cases i <;> norm_num [commonSixPrimes]

theorem commonSixPrimes_prod : ∏ i, commonSixPrimes i = 1926281441 := by
  norm_num [commonSixPrimes, Fin.prod_univ_succ]

theorem commonSixPrimes_prod_mod_eight : (∏ i, commonSixPrimes i) % 8 = 1 := by
  rw [commonSixPrimes_prod]

theorem commonSixPrimes_product_squarefree : Squarefree (1926281441 : ℕ) := by
  rw [← commonSixPrimes_prod]
  exact commonRootPrimeProduct_squarefree commonSixPrimes commonSixPrimes_prime
    commonSixPrimes_injective

/-- Every entry is evaluated from the Legendre symbol with the row prime as
its denominator, including the prescribed row-sum diagonal. -/
theorem commonSixPrimes_matrix_eq :
    primeLegendreMatrix commonSixPrimes commonSixPrimes_prime =
      !![0,1,0,1,1,1; 1,1,1,1,1,1; 1,1,0,0,0,0;
         0,1,1,1,1,0; 1,1,0,1,1,0; 0,1,1,1,0,1] := by
  have he : primeLegendreEntries commonSixPrimes commonSixPrimes_prime =
      !![0,1,0,1,1,1; 1,0,1,1,1,1; 1,1,0,0,0,0;
         0,1,1,0,1,0; 1,1,0,1,0,0; 0,1,1,1,0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [primeLegendreEntries,legendreBit,commonSixPrimes,Matrix.of_apply]
  unfold primeLegendreMatrix
  rw [he]
  decide

end FourCorner
