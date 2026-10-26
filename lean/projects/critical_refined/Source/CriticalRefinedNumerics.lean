import CriticalHasseNumerics

namespace FourCorner.CriticalRefinedNumerics

theorem count_gt_sixteen (q N:ℕ) (hq:29≤q)
    (hbound: |(N:ℝ)-((q:ℝ)+1)|≤2*Real.sqrt (q:ℝ)) : 16<N := by
  have hqR : (29:ℝ)≤(q:ℝ) := by exact_mod_cast hq
  have hs : 0≤Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (q:ℝ)^2=(q:ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
  have hl := (abs_le.mp hbound).1
  by_contra! hN
  have hNR : (N:ℝ)≤16 := by exact_mod_cast hN
  have hm : 0≤2*Real.sqrt (q:ℝ)-((q:ℝ)-15) := by linarith
  have hp : 0≤2*Real.sqrt (q:ℝ)+((q:ℝ)-15) := by linarith
  have hmul := mul_nonneg hm hp
  have hpoly : 0≤((q:ℝ)-29)*((q:ℝ)-5) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem count_gt_fortyEight (q N:ℕ) (hq:73≤q)
    (hbound: |(N:ℝ)-((q:ℝ)+1)|≤2*Real.sqrt (q:ℝ)) : 48<N := by
  have hqR : (73:ℝ)≤(q:ℝ) := by exact_mod_cast hq
  have hs : 0≤Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (q:ℝ)^2=(q:ℝ) := Real.sq_sqrt (Nat.cast_nonneg q)
  have hl := (abs_le.mp hbound).1
  by_contra! hN
  have hNR : (N:ℝ)≤48 := by exact_mod_cast hN
  have hm : 0≤2*Real.sqrt (q:ℝ)-((q:ℝ)-47) := by linarith
  have hp : 0≤2*Real.sqrt (q:ℝ)+((q:ℝ)-47) := by linarith
  have hmul := mul_nonneg hm hp
  have hpoly : 0≤((q:ℝ)-73)*((q:ℝ)-25) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem small_one_mod_eight (p:ℕ) (hp:p.Prime) (hmod:p%8=1) (hlt:p<73) : p=17 ∨ p=41 := by
  have hc : p=1 ∨ p=9 ∨ p=17 ∨ p=25 ∨ p=33 ∨ p=41 ∨ p=49 ∨ p=57 ∨ p=65 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at *

theorem small_five_mod_eight (p:ℕ) (hp:p.Prime) (hmod:p%8=5) (hlt:p<29) : p=5 ∨ p=13 := by
  have hc : p=5 ∨ p=13 ∨ p=21 := by omega
  rcases hc with rfl|rfl|rfl <;> norm_num at *

end FourCorner.CriticalRefinedNumerics
#print axioms FourCorner.CriticalRefinedNumerics.count_gt_sixteen
#print axioms FourCorner.CriticalRefinedNumerics.count_gt_fortyEight
#print axioms FourCorner.CriticalRefinedNumerics.small_one_mod_eight
#print axioms FourCorner.CriticalRefinedNumerics.small_five_mod_eight
