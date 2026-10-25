import OriginalFiniteChart

noncomputable section
namespace FourCorner.OriginalFiniteUnits
open AlgebraicCurve RadicalLinearization ResiduePlaceEvaluation OriginalFiniteOrders OriginalFiniteChart LinearizedFactors
variable {k : Type*} [Field k] [NeZero (2:k)] {t κ : k}
local notation "E" => CommonGenus17Field.field k t κ
attribute [local instance] Classical.propDecidable

theorem residue_zero_iff (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠0) (i : Fin 4) :
    evaluate w hw (originalSection h0 h1 hm hκ w hw hl ha i)=0 ↔
      evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩=branch t i.castSucc := by
  rw [ResidueValuationFacts.evaluate_zero_iff_ord_pos _ _ _ (original_ne_zero h1 hm hκ i)]
  change 0<w.ord (Genus17Geometry.fiveRoot t κ i.castSucc) ↔ _
  rw [original_order h0 h1 hm hκ w hw hl i]
  simp only [ha,and_false,ite_false,sub_zero]
  split_ifs <;> simp_all

theorem unit_iff (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (hκ : κ≠0)
    (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring)
    (ha : evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠0) (i : Fin 4) :
    IsUnit (originalSection h0 h1 hm hκ w hw hl ha i) ↔
      evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩≠branch t i.castSucc := by
  rw [←ResidueValuationFacts.evaluate_nonzero_iff_unit,ne_eq,residue_zero_iff h0 h1 hm hκ]
end FourCorner.OriginalFiniteUnits
#print axioms FourCorner.OriginalFiniteUnits.residue_zero_iff
#print axioms FourCorner.OriginalFiniteUnits.unit_iff
