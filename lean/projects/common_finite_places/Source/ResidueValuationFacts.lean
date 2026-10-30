import ResiduePlaceEvaluation
import OddFiveRamification

noncomputable section
namespace FourCorner.ResidueValuationFacts
open AlgebraicCurve ResiduePlaceEvaluation
variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem evaluate_zero_iff_residue_zero (w : Place k F) (hw : w.IsRational) (a : w.toValuationSubring) :
    evaluate w hw a=0 ↔ IsLocalRing.residue w.toValuationSubring a=0 := by
  let e := AlgEquiv.ofBijective (Algebra.ofId k w.ResidueField)
    ⟨(algebraMap k w.ResidueField).injective,hw⟩
  change e.symm (IsLocalRing.residue w.toValuationSubring a)=0 ↔ _
  constructor
  · intro h
    apply e.symm.injective
    simpa only [map_zero] using h
  · intro h
    rw [h,map_zero]

theorem evaluate_zero_iff_maximal (w : Place k F) (hw : w.IsRational) (a : w.toValuationSubring) :
    evaluate w hw a=0 ↔ a ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
  rw [evaluate_zero_iff_residue_zero,IsLocalRing.residue_eq_zero_iff]

theorem evaluate_nonzero_iff_unit (w : Place k F) (hw : w.IsRational) (a : w.toValuationSubring) :
    evaluate w hw a≠0 ↔ IsUnit a := by
  rw [ne_eq,evaluate_zero_iff_residue_zero]
  exact IsLocalRing.residue_ne_zero_iff_isUnit a

theorem evaluate_zero_iff_ord_pos (w : Place k F) (hw : w.IsRational) (a : w.toValuationSubring)
    (ha : (a:F)≠0) : evaluate w hw a=0 ↔ 0<w.ord (a:F) := by
  rw [evaluate_zero_iff_maximal]
  exact w.mem_maximalIdeal_iff_ord_pos ha a.property

theorem evaluate_nonzero_of_ord_zero (w : Place k F) (hw : w.IsRational) (a : w.toValuationSubring)
    (ha : (a:F)≠0) (ho : w.ord (a:F)=0) : evaluate w hw a≠0 := by
  apply (evaluate_nonzero_iff_unit w hw a).mpr
  apply (w.adicValuation_coe_eq_one_iff a).mp
  exact (w.ord_eq_zero_iff_adicValuation_eq_one ha).mp ho

theorem unit_of_ord_zero (w : Place k F) (a : w.toValuationSubring)
    (ha : (a:F)≠0) (ho : w.ord (a:F)=0) : IsUnit a :=
  (w.adicValuation_coe_eq_one_iff a).mp ((w.ord_eq_zero_iff_adicValuation_eq_one ha).mp ho)
end FourCorner.ResidueValuationFacts
#print axioms FourCorner.ResidueValuationFacts.evaluate_zero_iff_ord_pos
#print axioms FourCorner.ResidueValuationFacts.evaluate_nonzero_of_ord_zero
