import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false
namespace FourCorner.CriticalProjectiveCharacter
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

def product (V : Fin 4 → k) : k := V 0*V 3+V 1*V 2

/-- The actual integer-valued finite-field quadratic character is invariant
under every nonzero rescaling of the original projective coordinates. -/
theorem rescale (V : Fin 4 → k) (a : k) (ha : a≠0) :
    quadraticChar k (2*product (fun j=>a*V j))=
      quadraticChar k (2*product V) := by
  have h : 2*product (fun j=>a*V j)=a^2*(2*product V) := by
    dsimp [product]
    ring
  rw [h,map_mul,quadraticChar_sq_one' ha,one_mul]

end FourCorner.CriticalProjectiveCharacter
#print axioms FourCorner.CriticalProjectiveCharacter.rescale
