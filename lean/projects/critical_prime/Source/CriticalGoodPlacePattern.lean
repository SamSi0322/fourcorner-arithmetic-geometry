import CriticalFiniteGenus
import CriticalBadPlaces
import CriticalHasseNumerics

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open AlgebraicCurve
namespace FourCorner.CriticalGoodPlacePattern
open CriticalRadicalField ResiduePlaceEvaluation
variable {k : Type*} [Field k]

def unitPattern (i : k) : Prop :=
  ∃ s u v z : k, s ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧ z ≠ 0 ∧
    u^2 = 1+s ∧ v^2 = 1+i*s ∧ z^2 = 1+(1+i)*s

/-- All four entries come from evaluation at the SAME actual rational place
of the literal two-root field, with its original i and ordered coordinates. -/
theorem from_good_place (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (w : Place k (field k i)) (hw : w.IsRational) (hg : CriticalBadUnits.good i w) :
    unitPattern i := by
  obtain ⟨ha0,hb0,hc0,hs0⟩ := CriticalBadUnits.ordered_nonzero i hi h2
  obtain ⟨ha,hb,hc,hs⟩ := hg
  let ua : w.toValuationSubring := ⟨a k i,(w.mem_iff_ord_nonneg ha0).mpr (by rw [ha])⟩
  let ub : w.toValuationSubring := ⟨b k i,(w.mem_iff_ord_nonneg hb0).mpr (by rw [hb])⟩
  let uc : w.toValuationSubring := ⟨c k i,(w.mem_iff_ord_nonneg hc0).mpr (by rw [hc])⟩
  let us : w.toValuationSubring := ⟨a k i^2-1,(w.mem_iff_ord_nonneg hs0).mpr (by rw [hs])⟩
  have hshift : us = ua^2-1 := by apply Subtype.ext; rfl
  have hB : ub^2-1 = algebraMap k w.toValuationSubring i * (ua^2-1) := by
    apply Subtype.ext
    exact (actual_critical_equations k i).1
  have hC : uc^2-1 = algebraMap k w.toValuationSubring (1+i) * (ua^2-1) := by
    apply Subtype.ext
    exact (actual_critical_equations k i).2
  have hSval := congrArg (evaluate w hw) hshift
  have hBval := congrArg (evaluate w hw) hB
  have hCval := congrArg (evaluate w hw) hC
  simp only [map_sub,map_pow,map_one,map_mul,evaluate_constant] at hSval hBval hCval
  refine ⟨evaluate w hw us,evaluate w hw ua,evaluate w hw ub,evaluate w hw uc,
    ResidueValuationFacts.evaluate_nonzero_of_ord_zero w hw us hs0 hs,
    ResidueValuationFacts.evaluate_nonzero_of_ord_zero w hw ua ha0 ha,
    ResidueValuationFacts.evaluate_nonzero_of_ord_zero w hw ub hb0 hb,
    ResidueValuationFacts.evaluate_nonzero_of_ord_zero w hw uc hc0 hc,?_,?_,?_⟩
  · linear_combination -hSval
  · linear_combination hBval - i*hSval
  · linear_combination hCval - (1+i)*hSval

/-- The actual Hasse bound and the actual bad-place bound leave a good
degree-one place. The constants, genus and bad locus are proved internally. -/
theorem exists_good_place [Finite k] (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hq : 37 ≤ Nat.card k) :
    ∃ w : Place k (field k i), w.IsRational ∧ CriticalBadUnits.good i w := by
  have hH := CriticalFiniteGenus.hasse_bound k i hi h2
  have hN := CriticalHasseNumerics.count_gt_twentyFour (Nat.card k)
    (Nat.card {w : Place k (field k i) | w.deg=1}) hq hH.2
  have hB := CriticalBadPlaces.finite_and_card_le_twentyFour i hi h2
  by_contra! hnone
  have hsub : {w : Place k (field k i) | w.deg=1} ⊆ CriticalBadPlaces.bad i := by
    intro w hw
    exact ⟨hw,hnone w (w.isRational_iff_deg_eq_one.mpr hw)⟩
  have hc := Set.ncard_le_ncard hsub hB.1
  change Nat.card {w : Place k (field k i) | w.deg=1} ≤ Nat.card (CriticalBadPlaces.bad i) at hc
  omega

/-- Unconditional unit-pattern existence over every finite field of size
at least37 with i²=-1 and2 nonzero, retaining one common residue evaluation. -/
theorem exists_unit_pattern [Finite k] (i : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hq : 37 ≤ Nat.card k) : unitPattern i := by
  obtain ⟨w,hw,hg⟩ := exists_good_place i hi h2 hq
  exact from_good_place i hi h2 w hw hg

end FourCorner.CriticalGoodPlacePattern
#print axioms FourCorner.CriticalGoodPlacePattern.from_good_place
#print axioms FourCorner.CriticalGoodPlacePattern.exists_good_place
#print axioms FourCorner.CriticalGoodPlacePattern.exists_unit_pattern
