import CriticalBadUnits
import OddFifthUnramified

noncomputable section
namespace FourCorner.CriticalProductValuation
open AlgebraicCurve CriticalRadicalField
variable {k : Type*} [Field k]
set_option maxHeartbeats 1500000

def f (i:k) : field k i := c k i + a k i*b k i
def f' (i:k) : field k i := c k i - a k i*b k i

theorem product_identity (i:k) :
    f i*f' i = -algebraMap k (field k i) i*(a k i^2-1)^2 := by
  have hb:=b_squared k i
  have hc:=c_squared k i
  simp only [map_add,map_sub,map_one] at hb hc
  dsimp [f,f']
  linear_combination hc - (a k i)^2*hb

theorem nonzero (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) : f i≠0 ∧ f' i≠0 := by
  have h:=CriticalBadUnits.ordered_nonzero i hi h2
  have hi0:=CriticalElliptic23.iota_nonzero i hi
  have hp : f i*f' i≠0 := by
    rw [product_identity]
    exact mul_ne_zero (neg_ne_zero.mpr ((map_ne_zero _).mpr hi0)) (pow_ne_zero _ h.2.2.2)
  exact mul_ne_zero_iff.mp hp

lemma square_order (i:k) (w:Place k (field k i)) (x:field k i) :
    w.ord (x^2)=2*w.ord x := by simpa only [zpow_ofNat] using w.ord_zpow x (2:ℤ)

lemma integral_of_nonnegative (i:k) (w:Place k (field k i))
    (hi:i^2 = -1) (h2:(2:k)≠0) (ha:0≤w.ord (a k i)) :
    0≤w.ord (b k i) ∧ 0≤w.ord (c k i) ∧ 0≤w.ord (f i) ∧ 0≤w.ord (f' i) := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hf:=nonzero i hi h2
  have haM := (w.mem_iff_ord_nonneg hn.1).mpr ha
  have hbM : b k i^2 ∈ w.toValuationSubring := by
    rw [b_squared]
    exact w.toValuationSubring.add_mem _ _
      (w.toValuationSubring.mul_mem _ _ (w.algebraMap_mem' i) (w.toValuationSubring.pow_mem haM 2))
      (w.algebraMap_mem' (1-i))
  have hcM : c k i^2 ∈ w.toValuationSubring := by
    rw [c_squared]
    exact w.toValuationSubring.sub_mem
      (w.toValuationSubring.mul_mem _ _ (w.algebraMap_mem' (1+i)) (w.toValuationSubring.pow_mem haM 2))
      (w.algebraMap_mem' i)
  have hbN := (w.mem_iff_ord_nonneg (pow_ne_zero 2 hn.2.1)).mp hbM
  have hcN := (w.mem_iff_ord_nonneg (pow_ne_zero 2 hn.2.2.1)).mp hcM
  rw [square_order] at hbN hcN
  have hb : 0≤w.ord (b k i) := by omega
  have hc : 0≤w.ord (c k i) := by omega
  have hbI := (w.mem_iff_ord_nonneg hn.2.1).mpr hb
  have hcI := (w.mem_iff_ord_nonneg hn.2.2.1).mpr hc
  refine ⟨hb,hc,?_,?_⟩
  · apply (w.mem_iff_ord_nonneg hf.1).mp
    exact w.toValuationSubring.add_mem _ _ hcI (w.toValuationSubring.mul_mem _ _ haM hbI)
  · apply (w.mem_iff_ord_nonneg hf.2).mp
    exact w.toValuationSubring.sub_mem hcI (w.toValuationSubring.mul_mem _ _ haM hbI)

#print axioms product_identity
#print axioms nonzero
#print axioms integral_of_nonnegative
end FourCorner.CriticalProductValuation
