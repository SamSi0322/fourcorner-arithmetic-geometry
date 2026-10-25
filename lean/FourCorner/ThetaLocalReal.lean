import FourCorner.ThetaMetric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Set.Finite.Basic

namespace FourCorner

/-- The actual three source quadrics over the real numbers. -/
def RealThetaSource (P Q R z : ℝ) : Prop :=
  P ^ 2 = z ^ 2 + 50 ∧
  Q ^ 2 = z ^ 2 + 14 * z + 51 ∧
  R ^ 2 = z ^ 2 - 14 * z + 51

def RealThetaPositiveSource (P Q R z : ℝ) : Prop :=
  RealThetaSource P Q R z ∧ 1 < P ∧ 0 < Q ∧ 0 < R ∧ P + 7 * |z| < 50

def RealFourSquares (x y r₀ r₁ r₂ r₃ : ℝ) : Prop :=
  r₀ ^ 2 = x ^ 2 + y ^ 2 ∧
  r₁ ^ 2 = (1 - x) ^ 2 + y ^ 2 ∧
  r₂ ^ 2 = x ^ 2 + (1 - y) ^ 2 ∧
  r₃ ^ 2 = (1 - x) ^ 2 + (1 - y) ^ 2

/-- Real strict configurations; no rationality of any radius is asserted. -/
def RealStrictPoint (x y r₀ r₁ r₂ r₃ : ℝ) : Prop :=
  0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧
  0 < r₀ ∧ 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ ∧
  RealFourSquares x y r₀ r₁ r₂ r₃

theorem real_theta_positive_source_to_strict_point {P Q R z : ℝ}
    (h : RealThetaPositiveSource P Q R z) :
    RealStrictPoint ((50-P-7*z)/100) ((50-P+7*z)/100)
      ((P-1)/10) (Q/10) (R/10) ((P+1)/10) := by
  obtain ⟨⟨h₀, h₁, h₂⟩, hP, hQ, hR, hmetric⟩ := h
  have habs₁ := le_abs_self z
  have habs₂ := neg_le_abs z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (49/5000 : ℝ)*h₀
  · linear_combination (1/100 : ℝ)*h₁ - (1/5000 : ℝ)*h₀
  · linear_combination (1/100 : ℝ)*h₂ - (1/5000 : ℝ)*h₀
  · linear_combination (49/5000 : ℝ)*h₀

/-- The positive square roots are strict real sources throughout the interval. -/
theorem real_theta_small_positive_source {z : ℝ} (hz : 0 < z) (hzu : z ≤ 1/6) :
    RealThetaPositiveSource (Real.sqrt (z^2+50))
      (Real.sqrt (z^2+14*z+51)) (Real.sqrt (z^2-14*z+51)) z ∧
      Real.sqrt (z^2+50) < 8 := by
  have hp : 0 < z^2+50 := by nlinarith [sq_nonneg z]
  have hq : 0 < z^2+14*z+51 := by nlinarith [sq_nonneg (z+7)]
  have hr : 0 < z^2-14*z+51 := by nlinarith [sq_nonneg (z-7)]
  have hP := Real.sq_sqrt (le_of_lt hp)
  have hQ := Real.sq_sqrt (le_of_lt hq)
  have hR := Real.sq_sqrt (le_of_lt hr)
  have hPpos := Real.sqrt_pos.mpr hp
  have hQpos := Real.sqrt_pos.mpr hq
  have hRpos := Real.sqrt_pos.mpr hr
  have hP₁ : 1 < Real.sqrt (z^2+50) := by nlinarith [sq_nonneg z]
  have hPu : Real.sqrt (z^2+50) < 8 := by
    have hzz : z^2 ≤ (1/6 : ℝ)^2 := by nlinarith
    nlinarith
  refine ⟨⟨⟨hP, hQ, hR⟩, hP₁, hQpos, hRpos, ?_⟩, hPu⟩
  rw [abs_of_pos hz]
  linarith

/-- Explicit strict real four-distance configurations for small positive z. -/
theorem real_theta_small_strict_point {z : ℝ} (hz : 0 < z) (hzu : z ≤ 1/6) :
    RealStrictPoint
      ((50-Real.sqrt (z^2+50)-7*z)/100)
      ((50-Real.sqrt (z^2+50)+7*z)/100)
      ((Real.sqrt (z^2+50)-1)/10)
      (Real.sqrt (z^2+14*z+51)/10)
      (Real.sqrt (z^2-14*z+51)/10)
      ((Real.sqrt (z^2+50)+1)/10) :=
  real_theta_positive_source_to_strict_point (real_theta_small_positive_source hz hzu).1

/-- An infinite rational family; index k corresponds to exponent k+1. -/
def thetaLocalParameter (M k : ℕ) : ℚ := 1 / (M : ℚ)^(k+1)

theorem theta_local_parameter_bounds {M : ℕ} (hM : 6 ≤ M) (k : ℕ) :
    0 < thetaLocalParameter M k ∧ thetaLocalParameter M k ≤ 1/6 := by
  have hMr : (6 : ℚ) ≤ M := by exact_mod_cast hM
  have hMp : (0 : ℚ) < M := by linarith
  refine ⟨one_div_pos.mpr (pow_pos hMp _), ?_⟩
  have hp := one_div_pow_le_one_div_pow_of_le (a := (M : ℚ)) (by linarith : (1 : ℚ) ≤ M)
    (Nat.le_add_left 1 k)
  have hu : (1 : ℚ)/(M:ℚ) ≤ 1/6 :=
    (one_div_le_one_div hMp (by norm_num : (0 : ℚ) < 6)).mpr hMr
  exact le_trans (by simpa [thetaLocalParameter] using hp) hu

theorem theta_local_parameter_strictAnti {M : ℕ} (hM : 6 ≤ M) :
    StrictAnti (thetaLocalParameter M) := by
  have hMr : (6 : ℚ) ≤ M := by exact_mod_cast hM
  intro i j hij
  exact one_div_pow_lt_one_div_pow_of_lt (by linarith : (1 : ℚ) < M)
    (Nat.add_lt_add_right hij 1)

theorem theta_local_parameter_injective {M : ℕ} (hM : 6 ≤ M) :
    Function.Injective (thetaLocalParameter M) := (theta_local_parameter_strictAnti hM).injective

theorem theta_local_parameter_infinite {M : ℕ} (hM : 6 ≤ M) :
    Set.Infinite (Set.range (thetaLocalParameter M)) :=
  Set.infinite_range_of_injective (theta_local_parameter_injective hM)

theorem theta_local_parameter_real_sources {M : ℕ} (hM : 6 ≤ M) (k : ℕ) :
    ∃ P Q R : ℝ, RealThetaPositiveSource P Q R (thetaLocalParameter M k : ℝ) ∧ P < 8 := by
  obtain ⟨hp, hu⟩ := theta_local_parameter_bounds hM k
  have hp' : (0 : ℝ) < (thetaLocalParameter M k : ℝ) := by exact_mod_cast hp
  have hu' : (thetaLocalParameter M k : ℝ) ≤ 1/6 := by
    have hc : (thetaLocalParameter M k : ℝ) ≤ ((1/6 : ℚ) : ℝ) := by exact_mod_cast hu
    norm_num at hc ⊢
    exact hc
  exact ⟨_, _, _, real_theta_small_positive_source hp' hu'⟩

#print axioms real_theta_positive_source_to_strict_point
#print axioms real_theta_small_positive_source
#print axioms real_theta_small_strict_point
#print axioms theta_local_parameter_bounds
#print axioms theta_local_parameter_strictAnti
#print axioms theta_local_parameter_injective
#print axioms theta_local_parameter_infinite
#print axioms theta_local_parameter_real_sources
end FourCorner
