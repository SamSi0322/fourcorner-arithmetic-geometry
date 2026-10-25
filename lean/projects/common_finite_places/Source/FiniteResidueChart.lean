import RadicalLinearization
import ResiduePlaceEvaluation

noncomputable section
open AlgebraicCurve
namespace FourCorner.FiniteResidueChart
open RadicalLinearization ResiduePlaceEvaluation
variable {k : Type*} [Field k] (t κ : k) (hκ : κ ≠ 0)
local notation "E" => CommonGenus17Field.field k t κ

/-- Actual regular representatives of P,C,MZ,BZ,Z at the CHOSEN place. -/
def rootSection (w : Place k E) (hl : ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    w.toValuationSubring := by
  let l : w.toValuationSubring := ⟨ell k t κ,hl⟩
  let rhs := values (algebraMap k w.toValuationSubring t)
    (algebraMap k w.toValuationSubring κ⁻¹) l i
  have hrhs : (rhs : E) = values (algebraMap k E t) (algebraMap k E κ⁻¹) (ell k t κ) i := by
    exact map_values w.toValuationSubring.subtype _ _ _ i
  exact ⟨roots k t κ i, root_mem w (hrhs ▸ rhs.property) (roots_sq k t κ hκ i)⟩

theorem section_coe (w : Place k E) (hl : ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    (rootSection t κ hκ w hl i : E) = roots k t κ i := rfl

theorem section_sq (w : Place k E) (hl : ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    rootSection t κ hκ w hl i ^ 2 =
      values (algebraMap k w.toValuationSubring t) (algebraMap k w.toValuationSubring κ⁻¹)
        (⟨ell k t κ,hl⟩ : w.toValuationSubring) i := by
  apply Subtype.ext
  change roots k t κ i ^ 2 = _
  rw [roots_sq k t κ hκ i]
  exact (map_values w.toValuationSubring.subtype
    (algebraMap k w.toValuationSubring t) (algebraMap k w.toValuationSubring κ⁻¹)
      (⟨ell k t κ,hl⟩ : w.toValuationSubring) i).symm

/-- All five residues come from the SAME actual place and its actual
valuation-ring sections. This includes ell=0 and the four finite branch values. -/
theorem residue_equations (w : Place k E) (hw : w.IsRational)
    (hl : ell k t κ ∈ w.toValuationSubring) (i : Fin 5) :
    evaluate w hw (rootSection t κ hκ w hl i) ^ 2 =
      values t κ⁻¹ (evaluate w hw ⟨ell k t κ,hl⟩) i := by
  have h := congrArg (evaluate w hw) (section_sq t κ hκ w hl i)
  rw [map_pow] at h
  have hm := map_values (evaluate w hw).toRingHom
    (algebraMap k w.toValuationSubring t) (algebraMap k w.toValuationSubring κ⁻¹)
      (⟨ell k t κ,hl⟩ : w.toValuationSubring) i
  change (evaluate w hw) _ = values
    ((evaluate w hw) (algebraMap k w.toValuationSubring t))
    ((evaluate w hw) (algebraMap k w.toValuationSubring κ⁻¹))
      ((evaluate w hw) ⟨ell k t κ,hl⟩) i at hm
  rw [evaluate_constant,evaluate_constant] at hm
  exact h.trans hm

end FourCorner.FiniteResidueChart
#print axioms FourCorner.FiniteResidueChart.section_coe
#print axioms FourCorner.FiniteResidueChart.residue_equations
