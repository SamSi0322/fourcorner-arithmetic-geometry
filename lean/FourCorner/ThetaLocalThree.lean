import FourCorner.CriticalSeventeenPadic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace FourCorner

private instance prime3 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A square root of a 3-adic integer belongs to the 3-adic integers. -/
theorem theta3_root_integral (a : ℤ_[3]) (r : ℚ_[3])
    (hr : r ^ 2 = (a : ℚ_[3])) : ‖r‖ ≤ 1 := by
  have hsq : ‖r‖ * ‖r‖ ≤ 1 := by
    rw [← norm_mul, ← pow_two, hr]
    exact a.2
  nlinarith [norm_nonneg r]

/-- The residue class 2 is not a square in the field with three elements. -/
theorem theta3_residue_two_nonsquare (r : ZMod 3) : r ^ 2 ≠ 2 := by
  fin_cases r <;> decide

/-- For every residue of z, one of the three ordered radicands is 2 modulo 3. -/
theorem theta3_residue_obstruction (z P Q R : ZMod 3)
    (hP : P ^ 2 = z ^ 2 + 50)
    (hQ : Q ^ 2 = z ^ 2 + 14 * z + 51)
    (hR : R ^ 2 = z ^ 2 - 14 * z + 51) : False := by
  fin_cases z
  · exact theta3_residue_two_nonsquare P (by norm_num at hP ⊢; exact hP)
  · exact theta3_residue_two_nonsquare R (by norm_num at hR ⊢; exact hR)
  · exact theta3_residue_two_nonsquare Q (by norm_num at hQ ⊢; exact hQ)

/-- Simultaneous rational 3-adic roots of all three literal theta radicands
force the source coordinate outside the 3-adic integers. -/
theorem theta3_norm_gt_one_of_roots (z P Q R : ℚ_[3])
    (hP : P ^ 2 = z ^ 2 + 50)
    (hQ : Q ^ 2 = z ^ 2 + 14 * z + 51)
    (hR : R ^ 2 = z ^ 2 - 14 * z + 51) : 1 < ‖z‖ := by
  by_contra h
  have hz : ‖z‖ ≤ 1 := le_of_not_gt h
  let zi : ℤ_[3] := ⟨z, hz⟩
  let pi : ℤ_[3] := ⟨P, theta3_root_integral (zi ^ 2 + 50) P (by change P ^ 2 = z ^ 2 + 50; exact hP)⟩
  let qi : ℤ_[3] := ⟨Q, theta3_root_integral (zi ^ 2 + 14 * zi + 51) Q
    (by change Q ^ 2 = z ^ 2 + 14 * z + 51; exact hQ)⟩
  let ri : ℤ_[3] := ⟨R, theta3_root_integral (zi ^ 2 - 14 * zi + 51) R
    (by change R ^ 2 = z ^ 2 - 14 * z + 51; exact hR)⟩
  have hpi : pi ^ 2 = zi ^ 2 + 50 := by
    apply PadicInt.ext
    change P ^ 2 = z ^ 2 + 50
    exact hP
  have hqi : qi ^ 2 = zi ^ 2 + 14 * zi + 51 := by
    apply PadicInt.ext
    change Q ^ 2 = z ^ 2 + 14 * z + 51
    exact hQ
  have hri : ri ^ 2 = zi ^ 2 - 14 * zi + 51 := by
    apply PadicInt.ext
    change R ^ 2 = z ^ 2 - 14 * z + 51
    exact hR
  have hp := congrArg (PadicInt.toZMod : ℤ_[3] →+* ZMod 3) hpi
  have hq := congrArg (PadicInt.toZMod : ℤ_[3] →+* ZMod 3) hqi
  have hr := congrArg (PadicInt.toZMod : ℤ_[3] →+* ZMod 3) hri
  exact theta3_residue_obstruction (PadicInt.toZMod zi) (PadicInt.toZMod pi)
    (PadicInt.toZMod qi) (PadicInt.toZMod ri) (by simpa only [map_pow, map_add, map_ofNat] using hp)
    (by simpa only [map_pow, map_add, map_mul, map_ofNat] using hq) (by simpa only [map_pow, map_add, map_sub, map_mul, map_ofNat] using hr)

/-- The normalization of the p-adic valuation agrees with the norm formulation,
including the zero coordinate. -/
theorem theta_padic_norm_gt_one_iff_negative_valuation {p : ℕ} [Fact p.Prime]
    (z : ℚ_[p]) :
    1 < ‖z‖ ↔ z.valuation < 0 := by
  simpa only [not_le] using not_congr (Padic.norm_le_one_iff_val_nonneg z)

/-- Every actual simultaneous 3-adic source has negative coordinate valuation. -/
theorem theta3_valuation_neg_of_roots (z P Q R : ℚ_[3])
    (hP : P ^ 2 = z ^ 2 + 50)
    (hQ : Q ^ 2 = z ^ 2 + 14 * z + 51)
    (hR : R ^ 2 = z ^ 2 - 14 * z + 51) : z.valuation < 0 :=
  (theta_padic_norm_gt_one_iff_negative_valuation z).mp
    (theta3_norm_gt_one_of_roots z P Q R hP hQ hR)

/-- Existential form: every coordinate admitting the three simultaneous roots
lies in the negative-valuation locus of the actual completed field. -/
theorem theta3_valuation_neg_of_exists_roots (z : ℚ_[3])
    (h : ∃ P Q R : ℚ_[3], P ^ 2 = z ^ 2 + 50 ∧
      Q ^ 2 = z ^ 2 + 14 * z + 51 ∧ R ^ 2 = z ^ 2 - 14 * z + 51) :
    z.valuation < 0 := by
  obtain ⟨P, Q, R, hP, hQ, hR⟩ := h
  exact theta3_valuation_neg_of_roots z P Q R hP hQ hR

#print axioms theta3_root_integral
#print axioms theta3_residue_two_nonsquare
#print axioms theta3_residue_obstruction
#print axioms theta3_norm_gt_one_of_roots
#print axioms theta_padic_norm_gt_one_iff_negative_valuation
#print axioms theta3_valuation_neg_of_roots
#print axioms theta3_valuation_neg_of_exists_roots

end FourCorner
