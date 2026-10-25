import FourCorner.NineFlexGroup
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

namespace FourCorner

theorem small_A_root_nonsingular {x : ℚ} (hx : x=0 ∨ x=6 ∨ x=8) :
    (splitCurve 6 8).toAffine.Nonsingular x 0 := by
  rcases hx with rfl|rfl|rfl <;>
    norm_num [WeierstrassCurve.Affine.nonsingular_iff',
      WeierstrassCurve.Affine.equation_iff,splitCurve]

def smallAZeroRoot : (splitCurve 6 8).toAffine.Point :=
  .some 0 0 (small_A_root_nonsingular (Or.inl rfl))
def smallASixRoot : (splitCurve 6 8).toAffine.Point :=
  .some 6 0 (small_A_root_nonsingular (Or.inr (Or.inl rfl)))
def smallAEightRoot : (splitCurve 6 8).toAffine.Point :=
  .some 8 0 (small_A_root_nonsingular (Or.inr (Or.inr rfl)))

def smallAFourPoints : Fin 4 → (splitCurve 6 8).toAffine.Point :=
  ![0,smallAZeroRoot,smallASixRoot,smallAEightRoot]

lemma smallAFourPoints_injective : Function.Injective smallAFourPoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [smallAFourPoints,smallAZeroRoot,smallASixRoot,smallAEightRoot,
      WeierstrassCurve.Affine.Point.some.injEq]

/-- A cardinal bound becomes an exact list of actual elliptic points,
including the point at infinity. -/
theorem small_A_point_list_of_card [Finite (splitCurve 6 8).toAffine.Point]
    (hc : Nat.card (splitCurve 6 8).toAffine.Point ≤ 4)
    (P : (splitCurve 6 8).toAffine.Point) :
    P=0 ∨ P=smallAZeroRoot ∨ P=smallASixRoot ∨ P=smallAEightRoot := by
  have hs := (smallAFourPoints_injective.bijective_of_nat_card_le
    (by simpa using hc)).2
  obtain ⟨i, hi⟩ := hs P
  fin_cases i <;> simp only [smallAFourPoints, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at hi <;> simp_all

/-- The corresponding literal affine equation has no unlisted point. -/
theorem small_A_affine_points_of_card [Finite (splitCurve 6 8).toAffine.Point]
    (hc : Nat.card (splitCurve 6 8).toAffine.Point ≤ 4)
    {x y : ℚ} (h : y^2=x*(x-6)*(x-8)) :
    y=0 ∧ (x=0 ∨ x=6 ∨ x=8) := by
  have hn : (splitCurve 6 8).toAffine.Nonsingular x y := by
    rw [WeierstrassCurve.Affine.nonsingular_iff']
    refine ⟨(splitCurve_equation_iff 6 8 x y).mpr h, ?_⟩
    simp only [splitCurve]
    norm_num
    by_contra! hbad
    obtain ⟨hder,hy0⟩ := hbad
    rw [hy0] at h
    have hx : x=0 ∨ x=6 ∨ x=8 := by
      have hz : x*(x-6)*(x-8)=0 := by linarith
      rcases mul_eq_zero.mp hz with h|h
      · rcases mul_eq_zero.mp h with h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
    rcases hx with rfl|rfl|rfl <;> norm_num at hder
  have hp := small_A_point_list_of_card hc (.some x y hn)
  rcases hp with hp|hp|hp|hp
  · exact (WeierstrassCurve.Affine.Point.some_ne_zero hn hp).elim
  all_goals
    simp only [smallAZeroRoot,smallASixRoot,smallAEightRoot,
      WeierstrassCurve.Affine.Point.some.injEq] at hp
    rcases hp with ⟨rfl,rfl⟩ <;> simp

end FourCorner
#print axioms FourCorner.smallAFourPoints_injective
#print axioms FourCorner.small_A_affine_points_of_card
