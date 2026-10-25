import FourCorner.IntegralNormalization
import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false

namespace FourCorner

private def cornerEnvelope (k x y : ℝ) : ℝ := x + y - k*x*y

private theorem radius_lt_envelope {k x y r : ℝ}
    (_hk0 : 0 < k) (hk1 : k < 1) (hk : k^2 = 4*k-2)
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1)
    (hr0 : 0 < r) (hr : r^2 = x^2+y^2) :
    r < cornerEnvelope k x y := by
  have hky : k*y < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hk1) hy0]
  have hF : 0 < cornerEnvelope k x y := by
    unfold cornerEnvelope
    nlinarith [mul_pos hx0 (sub_pos.mpr hky)]
  have hid : (cornerEnvelope k x y)^2 - x^2-y^2 =
      x*y*(2*(1-x)*(1-y)+(2-2*k)*(x*(1-y)+(1-x)*y)) := by
    unfold cornerEnvelope
    linear_combination (x*y)^2 * hk
  have hinner : 0 < 2*(1-x)*(1-y)+(2-2*k)*(x*(1-y)+(1-x)*y) := by
    have hp1 := mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1)
    have hp2 := mul_pos hx0 (sub_pos.mpr hy1)
    have hp3 := mul_pos (sub_pos.mpr hx1) hy0
    have hp4 := mul_pos (show 0 < 2-2*k by linarith) (add_pos hp2 hp3)
    nlinarith
  have hprod := mul_pos (mul_pos hx0 hy0) hinner
  have hsq : r^2 < (cornerEnvelope k x y)^2 := by nlinarith [hid]
  exact (sq_lt_sq₀ (le_of_lt hr0) (le_of_lt hF)).mp hsq

/-- The sharp strict sum bound for the four labelled radii of an actual
strict rational point, proved using bilinear envelopes for each radius. -/
theorem strictPoint_radius_sum_lt {x y r₀ r₁ r₂ r₃ : ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    (r₀ : ℝ) + (r₁ : ℝ) + (r₂ : ℝ) + (r₃ : ℝ) < 2 + Real.sqrt 2 := by
  rcases h with ⟨hx₀, hx₁, hy₀, hy₁, hr₀, hr₁, hr₂, hr₃, hs₀, hs₁, hs₂, hs₃⟩
  let k : ℝ := 2 - Real.sqrt 2
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk0 : 0 < k := by dsimp [k]; nlinarith
  have hk1 : k < 1 := by dsimp [k]; nlinarith
  have hk : k ^ 2 = 4 * k - 2 := by dsimp [k]; nlinarith
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx₀
  have hx1 : (x : ℝ) < 1 := by exact_mod_cast hx₁
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy₀
  have hy1 : (y : ℝ) < 1 := by exact_mod_cast hy₁
  have hA0 : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
  have hB0 : (0 : ℝ) < r₁ := by exact_mod_cast hr₁
  have hC0 : (0 : ℝ) < r₂ := by exact_mod_cast hr₂
  have hD0 : (0 : ℝ) < r₃ := by exact_mod_cast hr₃
  have hAs : (r₀ : ℝ)^2 = (x : ℝ)^2 + (y : ℝ)^2 := by exact_mod_cast hs₀
  have hBs : (r₁ : ℝ)^2 = (1 - (x : ℝ))^2 + (y : ℝ)^2 := by exact_mod_cast hs₁
  have hCs : (r₂ : ℝ)^2 = (x : ℝ)^2 + (1 - (y : ℝ))^2 := by exact_mod_cast hs₂
  have hDs : (r₃ : ℝ)^2 = (1 - (x : ℝ))^2 + (1 - (y : ℝ))^2 := by exact_mod_cast hs₃
  have hA := radius_lt_envelope hk0 hk1 hk hx0 hx1 hy0 hy1 hA0 hAs
  have hB := radius_lt_envelope hk0 hk1 hk
    (show 0 < 1 - (x : ℝ) by linarith) (show 1 - (x : ℝ) < 1 by linarith)
    hy0 hy1 hB0 hBs
  have hC := radius_lt_envelope hk0 hk1 hk hx0 hx1
    (show 0 < 1 - (y : ℝ) by linarith) (show 1 - (y : ℝ) < 1 by linarith)
    hC0 hCs
  have hD := radius_lt_envelope hk0 hk1 hk
    (show 0 < 1 - (x : ℝ) by linarith) (show 1 - (x : ℝ) < 1 by linarith)
    (show 0 < 1 - (y : ℝ) by linarith) (show 1 - (y : ℝ) < 1 by linarith)
    hD0 hDs
  have hsum : cornerEnvelope k x y + cornerEnvelope k (1 - x) y +
      cornerEnvelope k x (1 - y) + cornerEnvelope k (1 - x) (1 - y) =
      2 + Real.sqrt 2 := by
    dsimp [cornerEnvelope, k]
    ring
  linarith

/-- The four positive integral radii satisfy the strict geometric sum bound.
No external geometric or analytic bound is assumed. -/
theorem IntegralModel.radius_sum_lt (P : IntegralModel) :
    (P.A₀ : ℝ) + (P.A₁ : ℝ) + (P.A₂ : ℝ) + (P.A₃ : ℝ) <
      (2 + Real.sqrt 2) * (P.L : ℝ) := by
  have h := strictPoint_radius_sum_lt P.toStrictPoint
  have h' : (P.A₀ : ℝ) / P.L + (P.A₁ : ℝ) / P.L +
      (P.A₂ : ℝ) / P.L + (P.A₃ : ℝ) / P.L < 2 + Real.sqrt 2 := by
    simpa only [Rat.cast_div, Rat.cast_intCast] using h
  have hL : (0 : ℝ) < P.L := by exact_mod_cast P.L_pos
  have hs : ((P.A₀ : ℝ) + (P.A₁ : ℝ) + (P.A₂ : ℝ) + (P.A₃ : ℝ)) / P.L <
      2 + Real.sqrt 2 := by simpa only [add_div] using h'
  simpa only [Int.cast_add] using (div_lt_iff₀ hL).mp hs

#print axioms strictPoint_radius_sum_lt
#print axioms IntegralModel.radius_sum_lt
end FourCorner
