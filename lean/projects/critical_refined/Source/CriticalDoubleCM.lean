import CriticalEllipticField
import CriticalDirectMap
import CriticalEllipticEvaluation
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace FourCorner.CriticalDoubleCM
variable {k : Type*} [Field k]

def xMap (i x : k) : k := -i*(x^2-1)/(2*x)
def yMap (i x y : k) : k := -(1+i)*y*(x^2+1)/(4*x^2)
def rootX (i x y : k) : k := (1-i)*y/(2*x)

theorem equation (i x y : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hx : x≠0) (hE : y^2=x^3-x) :
    yMap i x y ^2 = xMap i x ^3-xMap i x := by
  have h4 : (4:k)≠0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  have h16 : (16:k)≠0 := by convert pow_ne_zero 4 h2 using 1 <;> ring
  have hi3 : i^3 = -i := by
    calc
      i^3 = i^2*i := by ring
      _ = -i := by rw [hi]; ring
  dsimp [xMap,yMap]
  field_simp [h2,h4,h16,hx]
  rw [hE]
  ring_nf
  simp only [hi,hi3]
  ring

theorem root_square (i x y : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hx : x≠0) (hE : y^2=x^3-x) :
    rootX i x y ^2=xMap i x := by
  dsimp [rootX,xMap]
  field_simp
  rw [hE]
  ring_nf
  simp only [hi]
  ring


def recoverX (i X Y r : k) : k := i*(X+Y/r)
def recoverY (i X Y r : k) : k := (1+i)*recoverX i X Y r*r

theorem recover_x (i x y : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hx : x≠0) (hy : y≠0) :
    recoverX i (xMap i x) (yMap i x y) (rootX i x y)=x := by
  have hm : 1-i≠0 := CriticalQuarticCubic.scale_nonzero i hi h2
  have h4 : (4:k)≠0 := by convert pow_ne_zero 2 h2 using 1 <;> ring
  dsimp [recoverX,xMap,yMap,rootX]
  field_simp [h2,h4,hx,hy,hm]
  have hi3 : i^3 = -i := by
    rw [pow_succ,hi]
    ring
  ring_nf
  simp only [hi,hi3]
  ring

theorem recover_y (i x y : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hx : x≠0) (hy : y≠0) :
    recoverY i (xMap i x) (yMap i x y) (rootX i x y)=y := by
  rw [recoverY,recover_x i x y hi h2 hx hy]
  dsimp [rootX]
  field_simp [h2,hx]
  ring_nf
  simp only [hi]
  ring

/-- The self-map has genuinely transcendental abscissa. In particular its
native coordinate evaluator extends to an actual function-field embedding. -/
theorem map_transcendental {K L : Type*} [Field K] [Field L] [Algebra K L]
    (i x y : L) (hiA : IsAlgebraic K i) (hi : i^2 = -1) (h2 : (2:L)≠0)
    (hx : x≠0) (hy : y≠0) (hE : y^2=x^3-x) (ht : Transcendental K x) :
    Transcendental K (xMap i x) := by
  intro hX
  have hY : IsAlgebraic K (yMap i x y) := by
    have hs : IsIntegral K (yMap i x y ^2) := by
      rw [equation i x y hi h2 hx hE]
      exact (hX.isIntegral.pow 3).sub hX.isIntegral
    exact (IsIntegral.of_pow (n:=2) (by decide) hs).isAlgebraic
  have hr : IsAlgebraic K (rootX i x y) := by
    have hs : IsIntegral K (rootX i x y ^2) := by
      rw [root_square i x y hi h2 hx hE]
      exact hX.isIntegral
    exact (IsIntegral.of_pow (n:=2) (by decide) hs).isAlgebraic
  have hri : IsAlgebraic K (rootX i x y)⁻¹ := IsAlgebraic.inv_iff.mpr hr
  have hrx : IsAlgebraic K (recoverX i (xMap i x) (yMap i x y) (rootX i x y)) := by
    simpa only [recoverX,div_eq_mul_inv] using hiA.mul (hX.add (hY.mul hri))
  rw [recover_x i x y hi h2 hx hy] at hrx
  exact ht hrx

end FourCorner.CriticalDoubleCM
#print axioms FourCorner.CriticalDoubleCM.equation
#print axioms FourCorner.CriticalDoubleCM.root_square

#print axioms FourCorner.CriticalDoubleCM.recover_x
#print axioms FourCorner.CriticalDoubleCM.recover_y
#print axioms FourCorner.CriticalDoubleCM.map_transcendental
