import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
namespace FourCorner.CriticalHasseNumerics

/-- The exact numerical threshold used in the critical-prime theorem.
The input is an actual genus-one Hasse bound, not a point-existence premise. -/
theorem count_gt_twentyFour (q N : ℕ) (hq : 37 ≤ q)
    (hbound : |(N:ℝ) - ((q:ℝ)+1)| ≤ 2 * Real.sqrt (q:ℝ)) : 24 < N := by
  have hqR : (37:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hs : 0 ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (q:ℝ) ^ 2 = (q:ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
  have hlower := (abs_le.mp hbound).1
  by_contra! hN
  have hNR : (N:ℝ) ≤ 24 := by exact_mod_cast hN
  have hminus : 0 ≤ 2 * Real.sqrt (q:ℝ) - ((q:ℝ)-23) := by linarith
  have hplus : 0 ≤ 2 * Real.sqrt (q:ℝ) + ((q:ℝ)-23) := by linarith
  have hm := mul_nonneg hminus hplus
  have hp : 0 ≤ ((q:ℝ)-37) * ((q:ℝ)-13) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- A finite set with the actual point count has a point outside every
excluded locus of at most24 elements. The geometric excluded-locus bound
must still be proved for the intended curve. -/
theorem exists_outside {α : Type*} [DecidableEq α] (S B : Finset α)
    (hS : 24 < S.card) (hB : B.card ≤ 24) : ∃ x ∈ S, x ∉ B := by
  by_contra! h
  have hsub : S ⊆ B := h
  have hc := Finset.card_le_card hsub
  omega

end FourCorner.CriticalHasseNumerics
#print axioms FourCorner.CriticalHasseNumerics.count_gt_twentyFour
#print axioms FourCorner.CriticalHasseNumerics.exists_outside
