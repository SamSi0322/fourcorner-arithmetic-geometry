import CriticalBadCover
import RationalLinePlaceImage

noncomputable section
namespace FourCorner.CriticalBadUnits
open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField
open CriticalRadicalField
variable {k : Type*} [Field k]
local instance : DecidableEq (RatFunc k):=Classical.decEq _
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

/-- The exact ordered unit condition, including the original opposite shift. -/
def good (i : k) (w : Place k (field k i)) : Prop :=
  w.ord (a k i)=0 ∧ w.ord (b k i)=0 ∧ w.ord (c k i)=0 ∧ w.ord (a k i^2-1)=0

lemma shift_value (i : k) : polynomialValue k i (X^2-C 1)=a k i^2-1 := by
  simp only [map_sub,map_pow,polynomialValue_X,polynomialValue_C,map_one]

/-- All four global functions are genuinely nonzero. This prevents the
convention ord(0)=0 from being mistaken for a unit statement. -/
theorem ordered_nonzero (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    a k i≠0 ∧ b k i≠0 ∧ c k i≠0 ∧ a k i^2-1≠0 := by
  have hb : b k i^2≠0 := by
    rw [b,Biquadratic.root₁_sq]
    exact (_root_.map_ne_zero _).mpr (CriticalBranchPlaces.radicand_ne_zero i hi h2 0)
  have hc : c k i^2≠0 := by
    rw [c,Biquadratic.root₂_sq]
    exact (_root_.map_ne_zero _).mpr (CriticalBranchPlaces.radicand_ne_zero i hi h2 1)
  refine ⟨(_root_.map_ne_zero _).mpr RatFunc.X_ne_zero,?_,?_,?_⟩
  · intro hz;exact hb (by rw [hz,zero_pow (by decide : 2≠0)])
  · intro hz;exact hc (by rw [hz,zero_pow (by decide : 2≠0)])
  · rw [←shift_value]
    exact (_root_.map_ne_zero (algebraMap (RatFunc k) (field k i))).mpr
      (RatFunc.algebraMap_ne_zero (monic_X_pow_sub_C (1:k) (by decide : 2≠0)).ne_zero)

lemma ord_polynomial (i : k) (w : Place k (field k i)) (z : k)
    (hv : w.restrict (RatFunc k)=placeOfPoint k z) (p : k[X]) (hp : p.eval z≠0) :
    w.ord (polynomialValue k i p)=0 := by
  change w.ord (algebraMap (RatFunc k) (field k i) (algebraMap k[X] (RatFunc k) p))=0
  rw [w.ord_restrict,hv,OppositePlaceOrders.ord_polynomial_eq_zero_of_eval_ne_zero z hp,mul_zero]

/-- At a finite base value outside the explicit zeros, the SAME place has
all four original ordered functions of valuation order zero. -/
theorem finite_good (i : k) (w : Place k (field k i)) (z : k)
    (hv : w.restrict (RatFunc k)=placeOfPoint k z)
    (h0 : z≠0) (h1 : z≠1) (hm : z≠-1)
    (hB : (CriticalSquareclasses.qB i).eval z≠0) (hC : (CriticalSquareclasses.qC i).eval z≠0) :
    good i w := by
  have ha : w.ord (a k i)=0 := by
    have h:=ord_polynomial i w z hv X (by simpa only [eval_X] using h0)
    simpa only [polynomialValue_X] using h
  have hb : w.ord (b k i)=0 := by
    have h := ord_polynomial i w z hv (CriticalSquareclasses.qB i) hB
    have he : b k i^2=polynomialValue k i (CriticalSquareclasses.qB i) :=
      Biquadratic.root₁_sq (RatFunc k) _ _
    rw [←he] at h
    have hp : w.ord (b k i^2)=2*w.ord (b k i) := by
      simpa only [zpow_ofNat] using w.ord_zpow (b k i) (2:ℤ)
    rw [hp] at h
    omega
  have hc : w.ord (c k i)=0 := by
    have h := ord_polynomial i w z hv (CriticalSquareclasses.qC i) hC
    have he : c k i^2=polynomialValue k i (CriticalSquareclasses.qC i) :=
      Biquadratic.root₂_sq (RatFunc k) _ _
    rw [←he] at h
    have hp : w.ord (c k i^2)=2*w.ord (c k i) := by
      simpa only [zpow_ofNat] using w.ord_zpow (c k i) (2:ℤ)
    rw [hp] at h
    omega
  have hz : (X^2-C 1:k[X]).eval z≠0 := by
    simp only [eval_sub,eval_pow,eval_X,eval_C]
    intro h
    have hh : z^2=(1:k)^2 := by linear_combination h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with hh|hh
    · exact h1 hh
    · exact hm hh
  have hs := ord_polynomial i w z hv (X^2-C 1) hz
  rw [shift_value] at hs
  exact ⟨ha,hb,hc,hs⟩
end FourCorner.CriticalBadUnits
#print axioms FourCorner.CriticalBadUnits.ordered_nonzero
#print axioms FourCorner.CriticalBadUnits.finite_good
