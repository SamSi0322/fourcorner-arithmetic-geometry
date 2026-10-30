import FourCorner.CommonRootMatrixLinear
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

set_option maxRecDepth 10000
namespace FourCorner

open scoped Matrix BigOperators

/-- The six-prime common-root matrix, with rows completed to sum to zero. -/
def commonSixMatrix : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 1, 1, 1;
     1, 1, 1, 1, 1, 1;
     1, 1, 0, 0, 0, 0;
     0, 1, 1, 1, 1, 0;
     1, 1, 0, 1, 1, 0;
     0, 1, 1, 1, 0, 1]

/-- Symbolic elimination of the six row equations forces all coordinates
of a kernel vector to coincide. -/
theorem commonSixMatrix_kernel_constants (e : Fin 6 → ZMod 2) :
    commonSixMatrix.mulVec e = 0 ↔ ∀ i, e i = e 0 := by
  exact (by decide : ∀ v : Fin 6 → ZMod 2,
    commonSixMatrix.mulVec v = 0 ↔ ∀ i, v i = v 0) e
end FourCorner
