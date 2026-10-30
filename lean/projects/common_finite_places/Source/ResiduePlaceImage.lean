import LinearizedFactors
import ResidueValuationFacts

noncomputable section
namespace FourCorner.ResiduePlaceImage
open AlgebraicCurve AlgebraicCurve.RationalFunctionField RadicalLinearization ResiduePlaceEvaluation
variable {k : Type*} [Field k] [NeZero (2:k)] (t κ : k)
local notation "E" => CommonGenus17Field.field k t κ
local instance finiteLine : FiniteDimensional (RatFunc k) E := ResidueRadicalField.finite_over_line k t κ
local instance : DecidableEq (RatFunc k) := Classical.decEq _
set_option backward.isDefEq.respectTransparency.types false

theorem mapped_linear (a : k) :
    algebraMap (RatFunc k) E (OddFourPlaces.linear a) =
      RadicalLinearization.ell k t κ - algebraMap k E a := by
  rw [OddFourPlaces.linear_eq,map_sub]
  rfl

/-- A finite residue is the image of the SAME place on the ell line. -/
theorem finite_image (w : Place k E) (hw : w.IsRational)
    (hl : RadicalLinearization.ell k t κ ∈ w.toValuationSubring) :
    w.restrict (RatFunc k) = placeOfPoint k (evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩) := by
  let a := evaluate w hw ⟨RadicalLinearization.ell k t κ,hl⟩
  let f := algebraMap (RatFunc k) E (OddFourPlaces.linear a)
  have hf : f ≠ 0 := (map_ne_zero _).mpr (OddFourPlaces.linear_ne_zero a)
  have hmem : f ∈ w.toValuationSubring := by
    rw [show f = RadicalLinearization.ell k t κ-algebraMap k E a from mapped_linear t κ a]
    exact w.toValuationSubring.sub_mem hl (algebraMap k w.toValuationSubring a).property
  have he : evaluate w hw (⟨f,hmem⟩ : w.toValuationSubring)=0 := by
    have hid : (⟨f,hmem⟩ : w.toValuationSubring)=
      (⟨RadicalLinearization.ell k t κ,hl⟩ : w.toValuationSubring)-algebraMap k w.toValuationSubring a := by
      apply Subtype.ext
      exact mapped_linear t κ a
    rw [hid,map_sub,evaluate_constant]
    exact sub_self _
  have hp : 0<w.ord f := (ResidueValuationFacts.evaluate_zero_iff_ord_pos w hw ⟨f,hmem⟩ hf).mp he
  have ho := w.ord_restrict (OddFourPlaces.linear a)
  change w.ord f = _ at ho
  have hninf : w.restrict (RatFunc k) ≠ placeInfty k := by
    intro h
    rw [h,OddFourPlaces.ord_linear_infty] at ho
    have hepos : (0:ℤ)<w.ramificationIndex (RatFunc k) := by exact_mod_cast w.ramificationIndex_pos (F := RatFunc k)
    linarith
  by_contra hn
  rw [OddFourPlaces.ord_linear_off _ a hninf hn] at ho
  simp only [mul_zero] at ho
  omega

/-- A pole of ell lies over the genuine infinity place, including rational
places with nontrivial ramification above it. -/
theorem infinity_image (w : Place k E)
    (hl : RadicalLinearization.ell k t κ ∉ w.toValuationSubring) :
    w.restrict (RatFunc k) = placeInfty k := by
  have hneg : w.ord (RadicalLinearization.ell k t κ)<0 := by
    have := (w.mem_iff_ord_nonneg (ell_ne_zero k t κ)).not.mp hl
    omega
  have ho := w.ord_restrict (OddFourPlaces.linear (0:k))
  have heq : algebraMap (RatFunc k) E (OddFourPlaces.linear 0)=RadicalLinearization.ell k t κ := by
    rw [mapped_linear,map_zero,sub_zero]
  rw [heq] at ho
  by_contra hi
  by_cases hz : w.restrict (RatFunc k)=placeOfPoint k 0
  · rw [hz,OddFourPlaces.ord_linear_finite] at ho
    simp only [ite_true,mul_one] at ho
    have : (0:ℤ)<w.ramificationIndex (RatFunc k) := by exact_mod_cast w.ramificationIndex_pos (F := RatFunc k)
    omega
  · rw [OddFourPlaces.ord_linear_off _ 0 hi hz] at ho
    simp only [mul_zero] at ho
    omega
end FourCorner.ResiduePlaceImage
#print axioms FourCorner.ResiduePlaceImage.finite_image
#print axioms FourCorner.ResiduePlaceImage.infinity_image
