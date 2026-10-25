import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FourCorner

private instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The elementary residue obstruction used for the first theta-source equation. -/
theorem theta_mod_eight_square_classes (x : ZMod 8) :
    x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by
  fin_cases x <;> decide

theorem theta_mod_eight_no_square_difference (P z : ZMod 8) :
    P ^ 2 ≠ z ^ 2 + 50 := by
  intro h
  rcases theta_mod_eight_square_classes P with hP | hP | hP <;>
    rcases theta_mod_eight_square_classes z with hz | hz | hz <;>
    rw [hP, hz] at h <;> revert h <;> decide

/-- In the actual completed dyadic field the first equation forces a nonintegral
parameter. The argument first proves integrality of a proposed square root and
then reduces both integral elements modulo eight. -/
theorem theta_q2_first_square_norm_gt_one {P z : ℚ_[2]}
    (h : P ^ 2 = z ^ 2 + 50) : 1 < ‖z‖ := by
  by_contra hn
  have hz : ‖z‖ ≤ 1 := le_of_not_gt hn
  have hzsq : ‖z ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have h50 : ‖(50 : ℚ_[2])‖ ≤ 1 := by
    exact_mod_cast (Padic.norm_int_le_one (p := 2) 50)
  have hs : ‖P‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, h]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hzsq h50)
  have hP : ‖P‖ ≤ 1 := by nlinarith [norm_nonneg P]
  let Pi : ℤ_[2] := ⟨P, hP⟩
  let zi : ℤ_[2] := ⟨z, hz⟩
  have hi : Pi ^ 2 = zi ^ 2 + 50 := by
    apply PadicInt.ext
    exact h
  have hr := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) hi
  simp only [map_pow, map_add, map_ofNat] at hr
  exact theta_mod_eight_no_square_difference _ _ hr

/-- In particular any complete ordered theta source over `ℚ₂` has negative
two-adic valuation of its parameter, expressed without choosing a valuation
normalization by its norm being strictly greater than one. -/
theorem theta_q2_source_norm_gt_one {z : ℚ_[2]}
    (h : ∃ P Q R : ℚ_[2], P ^ 2 = z ^ 2 + 50 ∧
      Q ^ 2 = z ^ 2 + 14 * z + 51 ∧ R ^ 2 = z ^ 2 - 14 * z + 51) :
    1 < ‖z‖ := by
  obtain ⟨P, Q, R, hP, hQ, hR⟩ := h
  exact theta_q2_first_square_norm_gt_one hP

#print axioms theta_mod_eight_square_classes
#print axioms theta_mod_eight_no_square_difference
#print axioms theta_q2_first_square_norm_gt_one
#print axioms theta_q2_source_norm_gt_one

end FourCorner
