import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional
import Mathlib.Tactic

/-!
# Quadratic ramification at genuine places

The ramification index here is the index defined from the orders of an actual
valuation subring. Its upper bound is derived from the finite-fiber fundamental
identity. An odd order of a radicand then forces ramification index two in an
extension of degree at most two.
-/

noncomputable section

namespace FourCorner.QuadraticPlaceRamification

open AlgebraicCurve

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- Residue degrees in a finite extension are positive. -/
theorem inertiaDeg_pos (w : Place K E) : 0 < w.inertiaDeg F := by
  have := w.finite_residueField_of_finiteDimensional (F := F)
  exact Module.finrank_pos

/-- The genuine ramification index is bounded by the actual field degree. -/
theorem ramificationIndex_le_finrank (w : Place K E) :
    w.ramificationIndex F ≤ Module.finrank F E := by
  classical
  have hsum := (w.restrict F).sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := E)
  have hsingle :
      (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) ≤ (Module.finrank F E : ℤ) := by
    rw [← hsum]
    exact Finset.single_le_sum
      (fun u _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))
      (Place.restrict_mem_fiberOver (F := F) w)
  have hf : (1 : ℤ) ≤ (w.inertiaDeg F : ℤ) := by
    exact_mod_cast inertiaDeg_pos w
  have he : (0 : ℤ) ≤ (w.ramificationIndex F : ℤ) := Int.natCast_nonneg _
  have hle : (w.ramificationIndex F : ℤ) ≤ (Module.finrank F E : ℤ) := by
    nlinarith
  exact_mod_cast hle

/-- A square root of an element of odd order ramifies in a quadratic extension.
The hypothesis on the extension is only an upper bound on its actual finrank;
there is no supplied ramification or branch datum. -/
theorem ramificationIndex_eq_two_of_odd_ord
    (w : Place K E) {a : F} {r : E}
    (hroot : r ^ 2 = algebraMap F E a)
    (hodd : Odd ((w.restrict F).ord a))
    (hdegree : Module.finrank F E ≤ 2) :
    w.ramificationIndex F = 2 := by
  have hbound := (ramificationIndex_le_finrank w).trans hdegree
  have hpos := w.ramificationIndex_pos (F := F)
  have hord :
      (w.ramificationIndex F : ℤ) * (w.restrict F).ord a = 2 * w.ord r := by
    rw [← w.ord_restrict (F := F) a, ← hroot]
    simpa only [zpow_ofNat] using w.ord_zpow r (2 : ℤ)
  rcases hodd with ⟨k, hk⟩
  have hone_or_two : w.ramificationIndex F = 1 ∨ w.ramificationIndex F = 2 := by omega
  rcases hone_or_two with hone | htwo
  · rw [hone] at hord
    norm_num only [Nat.cast_one, one_mul] at hord
    omega
  · exact htwo

/-- The simple-zero form used at a branch point. -/
theorem ramificationIndex_eq_two_of_ord_eq_one
    (w : Place K E) {a : F} {r : E}
    (hroot : r ^ 2 = algebraMap F E a)
    (hord : (w.restrict F).ord a = 1)
    (hdegree : Module.finrank F E ≤ 2) :
    w.ramificationIndex F = 2 := by
  apply ramificationIndex_eq_two_of_odd_ord w hroot _ hdegree
  rw [hord]
  exact odd_one

end FourCorner.QuadraticPlaceRamification

#print axioms FourCorner.QuadraticPlaceRamification.ramificationIndex_le_finrank
#print axioms FourCorner.QuadraticPlaceRamification.ramificationIndex_eq_two_of_odd_ord
#print axioms FourCorner.QuadraticPlaceRamification.ramificationIndex_eq_two_of_ord_eq_one
