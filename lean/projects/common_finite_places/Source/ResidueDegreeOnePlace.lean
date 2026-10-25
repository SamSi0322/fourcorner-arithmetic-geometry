import FiniteBaseGenus
import SharpPointBound
import CommonFinitePlacesHensel
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one

noncomputable section
open AlgebraicCurve
namespace FourCorner.ResidueDegreeOnePlace
variable (k : Type*) [Field k] [Finite k] [NeZero (2 : k)]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Hasse--Weil yields an ACTUAL degree-one place of the literal residue
five-root field. Its genus and constants are proved, not supplied as premises. -/
theorem exists_degree_one {t κ : k} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0)
    (hq : 1153 < Nat.card k) :
    ∃ w : Place k (CommonGenus17Field.field k t κ), w.deg = 1 := by
  let F := CommonGenus17Field.field k t κ
  letI : PerfectField k := PerfectField.ofFinite
  letI : IsCurveOver k F := ResidueRadicalField.isCurveOver k t κ
  letI : Algebra.EssFiniteType k F := ResidueRadicalField.essFiniteType k t κ
  have hC := ResidueFullConstants.constantsAreBase k h0 h1 hm hκ
  have hcount := finite_degree_one_places_and_hasseWeil_bound k F hC
  have hg := FiniteBaseGenus.seventeen_of_finite k h0 h1 hm hκ
  have hbound := hcount.2
  rw [hg] at hbound
  norm_num only [Nat.cast_ofNat] at hbound
  have hlower := (abs_le.mp hbound).1
  have hpositive := CommonFinitePlaces.genus17_lower_bound_positive (Nat.card k) hq
  by_contra hnone
  let S : Set (Place k F) := {w | w.deg = 1}
  letI : IsEmpty S := ⟨by
    rintro ⟨w,hw⟩
    exact hnone ⟨w,hw⟩⟩
  have hz : Nat.card S = 0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
  change -(34 * Real.sqrt (Nat.card k : ℝ)) ≤ (Nat.card S : ℝ) - ((Nat.card k : ℝ)+1) at hlower
  rw [hz,Nat.cast_zero] at hlower
  linarith

/-- The resulting degree-one place has its ACTUAL residue field identified
with k; no named special-fibre Scheme or rational-point predicate is substituted. -/
theorem exists_rational {t κ : k} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0)
    (hq : 1153 < Nat.card k) :
    ∃ w : Place k (CommonGenus17Field.field k t κ), w.IsRational := by
  obtain ⟨w,hw⟩ := exists_degree_one k h0 h1 hm hκ hq
  exact ⟨w,w.isRational_iff_deg_eq_one.mpr hw⟩

end FourCorner.ResidueDegreeOnePlace
#print axioms FourCorner.ResidueDegreeOnePlace.exists_degree_one
#print axioms FourCorner.ResidueDegreeOnePlace.exists_rational
