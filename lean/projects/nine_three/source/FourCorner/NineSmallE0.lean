import FourCorner.NineFlexGroup
import FourCorner.SquarefreePart
import FourCorner.NineSmallE0Local
import FourCorner.NineSmallASignedSupport
import Mathlib.Tactic

/-! Arithmetic data for the small curve `y²=x(x+1)(x+4)`. -/

namespace FourCorner.NineSmallE0

def OnCurve (x y : ℚ) : Prop := y ^ 2 = x * (x + 1) * (x + 4)

/-- The four signed ordered Kummer rows, represented without sign removal. -/
def Row (x : ℚ) : Prop :=
  (∃ a b c : ℚ, x = a^2 ∧ x+1 = b^2 ∧ x+4 = c^2) ∨
  (∃ a b c : ℚ, x = -a^2 ∧ x+1 = -3*b^2 ∧ x+4 = 3*c^2) ∨
  (∃ a b c : ℚ, x = 2*a^2 ∧ x+1 = 3*b^2 ∧ x+4 = 6*c^2) ∨
  (∃ a b c : ℚ, x = -2*a^2 ∧ x+1 = -b^2 ∧ x+4 = 2*c^2)

lemma signed_divisor_four {d : ℤ} (hd : d ∣ 4) (hs : Squarefree d.natAbs) :
    d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2 := by
  have hb := Int.natAbs_le_of_dvd_ne_zero hd (by norm_num)
  norm_num at hb
  have hlo : -4 ≤ d := by omega
  have hhi : d ≤ 4 := by omega
  have hn4 : ¬Squarefree (4 : ℕ) := by decide
  interval_cases d <;> norm_num at * <;> contradiction

lemma signed_divisor_neg_three {d : ℤ} (hd : d ∣ -3) :
    d = 1 ∨ d = -1 ∨ d = 3 ∨ d = -3 := by
  have hb := Int.natAbs_le_of_dvd_ne_zero hd (by norm_num)
  norm_num at hb
  have hlo : -3 ≤ d := by omega
  have hhi : d ≤ 3 := by omega
  interval_cases d <;> norm_num at *

/-- An ordinary affine point has both initial root differences of the same
sign. This excludes the other real sign patterns before local descent. -/
lemma first_two_same_sign {x y : ℚ} (h : OnCurve x y) (hx : x ≠ 0)
    (hx1 : x+1 ≠ 0) (hx4 : x+4 ≠ 0) :
    (0 < x ∧ 0 < x+1) ∨ (x < 0 ∧ x+1 < 0) := by
  have hy : y ≠ 0 := by
    intro he
    simp only [OnCurve, he, zero_pow (by decide : 2 ≠ 0)] at h
    have hz : x * (x+1) * (x+4) = 0 := h.symm
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact hx hz
      · exact hx1 hz
    · exact hx4 hz
  have hp : 0 < x * (x+1) * (x+4) := by rw [← h]; exact sq_pos_of_ne_zero hy
  by_cases hxp : 0 < x
  · exact Or.inl ⟨hxp, by linarith⟩
  · have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx
    right
    refine ⟨hxn, ?_⟩
    by_contra hxn1
    have hp1 : 0 < x+1 := lt_of_le_of_ne (le_of_not_gt hxn1) (Ne.symm hx1)
    have hp4 : 0 < x+4 := by linarith
    have : x * (x+1) * (x+4) < 0 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hxn hp1) hp4
    linarith

/-- Recover the third ordered square from the first two, retaining the
literal product and its rational scale. -/
lemma third_square {x y d e a b : ℚ} (h : OnCurve x y)
    (hx : x = d*a^2) (hx1 : x+1 = e*b^2)
    (hd : d ≠ 0) (he : e ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    x+4 = (d*e) * (y/(d*e*a*b))^2 := by
  unfold OnCurve at h
  field_simp
  calc
    (x + 4) * d * e * a ^ 2 * b ^ 2 = (d*a^2)*(e*b^2)*(x+4) := by ring
    _ = x * (x+1) * (x+4) := by rw [← hx, ← hx1]
    _ = y^2 := h.symm

/-- The complete ordered square-class bound for ordinary rational points. -/
theorem ordinary_row {x y : ℚ} (h : OnCurve x y) (hx0 : x ≠ 0)
    (hx1z : x+1 ≠ 0) (hx4z : x+4 ≠ 0) : Row x := by
  obtain ⟨d, hds, hd, a, ha, hx⟩ := cubic_signed_squarefree_support
    (a := 5) (b := 4) (by norm_num) hx0 (by norm_num; unfold OnCurve at h; nlinarith [h])
  obtain ⟨e, _, he, b, hb, hx1⟩ := cubic_signed_squarefree_support
    (a := 2) (b := -3) (x := x+1) (y := y) (by norm_num) hx1z
    (by norm_num; unfold OnCurve at h; nlinarith [h])
  have hd0 : (d : ℚ) ≠ 0 := by intro hz; rw [hz, zero_mul] at hx; exact hx0 hx
  have he0 : (e : ℚ) ≠ 0 := by intro hz; rw [hz, zero_mul] at hx1; exact hx1z hx1
  let c : ℚ := y / ((d : ℚ)*e*a*b)
  have hx4 : x+4 = ((d : ℚ)*e)*c^2 := third_square h hx hx1 hd0 he0 ha.ne' hb.ne'
  have hsgn := first_two_same_sign h hx0 hx1z hx4z
  rcases signed_divisor_four hd hds with hd | hd | hd | hd <;>
    rcases signed_divisor_neg_three he with he | he | he | he <;>
    subst d <;> subst e <;> norm_num at hx hx1 hx4
  all_goals simp only [Row, neg_mul]
  all_goals first
    | exact Or.inl ⟨a, b, c, hx, hx1, hx4⟩
    | exact Or.inr (Or.inl ⟨a, b, c, hx, hx1, hx4⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨a, b, c, hx, hx1, hx4⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨a, b, c, hx, hx1, hx4⟩))
    | exact (not_row_one_three_three x a b c hx hx1 hx4).elim
    | exact (not_row_two_one_two x a b c hx hx1 hx4).elim
    | exact (not_row_neg_one_neg_one_one x a b c hx hx1 hx4).elim
    | exact (not_row_neg_two_neg_three_six x a b c (by simpa only [neg_mul] using hx)
        (by simpa only [neg_mul] using hx1) hx4).elim
    | rcases hsgn with hs | hs <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]

/-- The square-row statement also covers all three rational roots. At roots
the actual Kummer map must use its cofactor convention. -/
theorem affine_row {x y : ℚ} (h : OnCurve x y) : Row x := by
  by_cases hx0 : x = 0
  · subst x; exact Or.inl ⟨0, 1, 2, by norm_num, by norm_num, by norm_num⟩
  by_cases hx1 : x+1 = 0
  · have hx : x = -1 := by linarith
    subst x
    exact Or.inr (Or.inl ⟨1, 0, 1, by norm_num, by norm_num, by norm_num⟩)
  by_cases hx4 : x+4 = 0
  · have hx : x = -4 := by linarith
    subst x
    exact Or.inr (Or.inl ⟨2, 1, 0, by norm_num, by norm_num, by norm_num⟩)
  exact ordinary_row h hx0 hx1 hx4

end FourCorner.NineSmallE0

#print axioms FourCorner.NineSmallE0.signed_divisor_four
#print axioms FourCorner.NineSmallE0.first_two_same_sign
#print axioms FourCorner.NineSmallE0.third_square
#print axioms FourCorner.NineSmallE0.ordinary_row
#print axioms FourCorner.NineSmallE0.affine_row
