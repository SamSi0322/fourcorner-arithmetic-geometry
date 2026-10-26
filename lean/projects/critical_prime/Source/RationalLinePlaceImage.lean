import CriticalActualRamification
import OddFourPlaces
import ResidueValuationFacts

noncomputable section
namespace FourCorner.RationalLinePlaceImage
open AlgebraicCurve AlgebraicCurve.RationalFunctionField ResiduePlaceEvaluation
variable {k E : Type*} [Field k] [Field E] [Algebra k E]
    [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E]
    [FiniteDimensional (RatFunc k) E] [NeZero (2:k)]
abbrev parameter : E:=algebraMap (RatFunc k) E RatFunc.X
lemma parameter_ne_zero : (parameter (k:=k) (E:=E))≠0 :=
  (_root_.map_ne_zero _).mpr RatFunc.X_ne_zero
local instance : DecidableEq (RatFunc k) := Classical.decEq _
set_option backward.isDefEq.respectTransparency.types false

theorem mapped_linear (a : k) :
    algebraMap (RatFunc k) E (OddFourPlaces.linear a) =
      parameter (k:=k) (E:=E) - algebraMap k E a := by
  rw [OddFourPlaces.linear_eq,map_sub]
  rw [←IsScalarTower.algebraMap_apply k (RatFunc k) E]

/-- A finite residue is the image of the SAME place on the ell line. -/
theorem finite_image (w : Place k E) (hw : w.IsRational)
    (hl : parameter (k:=k) (E:=E) ∈ w.toValuationSubring) :
    w.restrict (RatFunc k) = placeOfPoint k (evaluate w hw ⟨parameter (k:=k) (E:=E),hl⟩) := by
  let a := evaluate w hw ⟨parameter (k:=k) (E:=E),hl⟩
  let f := algebraMap (RatFunc k) E (OddFourPlaces.linear a)
  have hf : f ≠ 0 := (map_ne_zero _).mpr (OddFourPlaces.linear_ne_zero a)
  have hmem : f ∈ w.toValuationSubring := by
    rw [show f = parameter (k:=k) (E:=E)-algebraMap k E a from mapped_linear (E:=E) a]
    exact w.toValuationSubring.sub_mem hl (algebraMap k w.toValuationSubring a).property
  have he : evaluate w hw (⟨f,hmem⟩ : w.toValuationSubring)=0 := by
    have hid : (⟨f,hmem⟩ : w.toValuationSubring)=
      (⟨parameter (k:=k) (E:=E),hl⟩ : w.toValuationSubring)-algebraMap k w.toValuationSubring a := by
      apply Subtype.ext
      exact mapped_linear (E:=E) a
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
    (hl : parameter (k:=k) (E:=E) ∉ w.toValuationSubring) :
    w.restrict (RatFunc k) = placeInfty k := by
  have hneg : w.ord (parameter (k:=k) (E:=E))<0 := by
    have := (w.mem_iff_ord_nonneg (parameter_ne_zero (k:=k) (E:=E))).not.mp hl
    omega
  have ho := w.ord_restrict (OddFourPlaces.linear (0:k))
  have heq : algebraMap (RatFunc k) E (OddFourPlaces.linear 0)=parameter (k:=k) (E:=E) := by
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
end FourCorner.RationalLinePlaceImage

#print axioms FourCorner.RationalLinePlaceImage.finite_image
#print axioms FourCorner.RationalLinePlaceImage.infinity_image
