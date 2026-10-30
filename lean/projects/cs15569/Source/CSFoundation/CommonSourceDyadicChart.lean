import FourCorner.CommonRootPadicVal
import FourCorner.ThetaLocalHensel

set_option autoImplicit false

noncomputable section

namespace FourCorner

/-- The finite affine chart on `y²=x(x-n)(x+n)` sufficiently close to infinity.
All coordinates are elements of the actual dyadic field. -/
structure CommonSourceDyadicPoint (n : ℚ_[2]) where
  x : ℚ_[2]
  y : ℚ_[2]
  equation : y ^ 2 = x * (x - n) * (x + n)
  depth_bound : x.valuation ≤ -4

namespace CommonSourceDyadicPoint

variable {n : ℚ_[2]} (P : CommonSourceDyadicPoint n)

theorem x_ne_zero : P.x ≠ 0 := by
  intro h
  have hd := P.depth_bound
  simp [h] at hd

/-- The inverse abscissa is in `16ℤ₂`. -/
theorem norm_inv_x_le : ‖P.x⁻¹‖ ≤ (1 / 16 : ℝ) := by
  rw [Padic.norm_eq_zpow_neg_valuation (inv_ne_zero P.x_ne_zero), Padic.valuation_inv]
  have h := (zpow_le_zpow_iff_right₀ (show (1 : ℝ) < 2 by norm_num)).mpr P.depth_bound
  norm_num at h ⊢
  exact h

/-- The linear unit corrections are small at every permitted depth. -/
theorem norm_n_div_x_le (hn : ‖n‖ ≤ 1) : ‖n / P.x‖ ≤ (1 / 16 : ℝ) := by
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ 1 * (1 / 16 : ℝ) :=
      mul_le_mul hn P.norm_inv_x_le (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

/-- The two linear corrections and the quadratic cubic correction are local squares. -/
theorem corrections_isSquare (hn : ‖n‖ ≤ 1) :
    IsSquare (1 + n / P.x) ∧ IsSquare (1 - n / P.x) ∧
      IsSquare (1 - (n / P.x) ^ 2) := by
  have h := P.norm_n_div_x_le hn
  have hsq : ‖n / P.x‖ ^ 2 ≤ (1 / 16 : ℝ)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  refine ⟨padic_two_isSquare_one_add _ (by linarith), ?_, ?_⟩
  · simpa only [sub_eq_add_neg] using
      padic_two_isSquare_one_add (-(n / P.x)) (by simpa only [norm_neg] using (show ‖n / P.x‖ < (1 / 4 : ℝ) by linarith))
  · simpa only [sub_eq_add_neg] using
      padic_two_isSquare_one_add (-((n / P.x)^2)) (by
        rw [norm_neg, norm_pow]
        norm_num at hsq ⊢
        linarith)

/-- The cubic itself supplies the missing square class of the abscissa. -/
theorem local_squares (hn : ‖n‖ ≤ 1) :
    IsSquare P.x ∧ IsSquare (P.x - n) ∧ IsSquare (P.x + n) := by
  obtain ⟨hp, hm, hc⟩ := P.corrections_isSquare hn
  have hc0 : 1 - (n / P.x) ^ 2 ≠ 0 := by
    intro hz
    have he : (n / P.x)^2 = 1 := by linear_combination -hz
    have hnorm := congrArg norm he
    rw [norm_pow, norm_one] at hnorm
    have h := P.norm_n_div_x_le hn
    have hsq := pow_le_pow_left₀ (norm_nonneg (n / P.x)) h 2
    norm_num only [show (1 / 16 : ℝ)^2 = 1 / 256 by norm_num] at hsq
    linarith
  have hid : (P.y / P.x)^2 = P.x * (1 - (n / P.x)^2) := by
    field_simp [P.x_ne_zero]
    linear_combination P.equation
  have hx : IsSquare P.x := by
    have he : P.x = (P.y / P.x)^2 / (1 - (n / P.x)^2) := by
      apply (eq_div_iff hc0).2
      exact hid.symm
    rw [he]
    exact (IsSquare.sq _).div hc
  refine ⟨hx, ?_, ?_⟩
  · have he : P.x - n = P.x * (1 - n / P.x) := by field_simp [P.x_ne_zero]
    rw [he]
    exact hx.mul hm
  · have he : P.x + n = P.x * (1 + n / P.x) := by field_simp [P.x_ne_zero]
    rw [he]
    exact hx.mul hp

/-- Translation by an integral parameter does not change a negative abscissa valuation. -/
theorem valuation_offsets (hn : ‖n‖ ≤ 1) :
    (P.x - n).valuation = P.x.valuation ∧ (P.x + n).valuation = P.x.valuation := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnval := (Padic.norm_le_one_iff_val_nonneg n).mp hn
  have hlt : P.x.valuation < n.valuation := by have := P.depth_bound; omega
  constructor
  · rw [commonRoot_val_sub_of_ne P.x_ne_zero hn0 (ne_of_lt hlt), min_eq_left (le_of_lt hlt)]
  · rw [commonRoot_val_add_of_ne P.x_ne_zero hn0 (ne_of_lt hlt), min_eq_left (le_of_lt hlt)]

theorem offsets_ne_zero (hn : ‖n‖ ≤ 1) : P.x - n ≠ 0 ∧ P.x + n ≠ 0 := by
  obtain ⟨hm, hp⟩ := P.valuation_offsets hn
  constructor <;> intro he
  · rw [he, Padic.valuation_zero] at hm
    have := P.depth_bound
    omega
  · rw [he, Padic.valuation_zero] at hp
    have := P.depth_bound
    omega

theorem y_ne_zero (hn : ‖n‖ ≤ 1) : P.y ≠ 0 := by
  obtain ⟨hm, hp⟩ := P.offsets_ne_zero hn
  intro hy
  have he := P.equation
  rw [hy, zero_pow (by decide)] at he
  exact (mul_ne_zero (mul_ne_zero P.x_ne_zero hm) hp) he.symm

/-- The ordinate valuation is forced by the cubic, with no depth truncation. -/
theorem valuation_equation (hn : ‖n‖ ≤ 1) :
    2 * P.y.valuation = 3 * P.x.valuation := by
  obtain ⟨hm0, hp0⟩ := P.offsets_ne_zero hn
  obtain ⟨hm, hp⟩ := P.valuation_offsets hn
  have he := congrArg Padic.valuation P.equation
  rw [Padic.valuation_pow, Padic.valuation_mul (mul_ne_zero P.x_ne_zero hm0) hp0,
    Padic.valuation_mul P.x_ne_zero hm0, hm, hp] at he
  norm_num at he
  omega

/-- The geometric depth, normalized so `v₂(x)=-2j`. -/
def depth : ℕ := (-(P.x.valuation / 2)).toNat

/-- The depth is an integer at least two, not an assumed half-valuation. -/
theorem depth_spec (hn : ‖n‖ ≤ 1) :
    2 ≤ P.depth ∧ P.x.valuation = -2 * (P.depth : ℤ) ∧
      P.y.valuation = -3 * (P.depth : ℤ) := by
  obtain ⟨k, hk⟩ := commonRoot_even_val_of_isSquare (P.local_squares hn).1
  have hk2 : k ≤ -2 := by have := P.depth_bound; omega
  have hv : P.x.valuation / 2 = k := by omega
  have hd : (P.depth : ℤ) = -k := by
    simp only [depth, hv, Int.toNat_of_nonneg (by omega : 0 ≤ -k)]
  have he := P.valuation_equation hn
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Normalize the square root of the abscissa by its precise depth.
The remaining square root is a genuine unit of the dyadic field. -/
theorem normalized_square (hn : ‖n‖ ≤ 1) :
    ∃ r : ℚ_[2], r ≠ 0 ∧ r.valuation = 0 ∧
      P.x = (r / (2 : ℚ_[2]) ^ P.depth) ^ 2 := by
  obtain ⟨t, ht⟩ := (P.local_squares hn).1
  have ht0 : t ≠ 0 := by
    intro h
    exact P.x_ne_zero (by simpa [h] using ht)
  have htval : t.valuation = -(P.depth : ℤ) := by
    have he := congrArg Padic.valuation ht
    rw [Padic.valuation_mul ht0 ht0] at he
    have hd := (P.depth_spec hn).2.1
    omega
  have htwo : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hv2 : (2 : ℚ_[2]).valuation = 1 := by exact Padic.valuation_p (p := 2)
  refine ⟨t * (2 : ℚ_[2]) ^ P.depth,
    mul_ne_zero ht0 (pow_ne_zero _ htwo), ?_, ?_⟩
  · rw [Padic.valuation_mul ht0 (pow_ne_zero _ htwo), Padic.valuation_pow,
      hv2, htval]
    ring
  · rw [mul_div_cancel_right₀ t (pow_ne_zero P.depth htwo), pow_two]
    exact ht

/-- The standard parameter at infinity. -/
def z : ℚ_[2] := -P.x / P.y

/-- The exact unit factor in the formal chart. -/
def W : ℚ_[2] := P.y ^ 2 / P.x ^ 3

theorem z_ne_zero (hn : ‖n‖ ≤ 1) : P.z ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr P.x_ne_zero) (P.y_ne_zero hn)

theorem W_ne_zero (hn : ‖n‖ ≤ 1) : P.W ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (P.y_ne_zero hn)) (pow_ne_zero _ P.x_ne_zero)

/-- The formal parameter has exactly the geometric depth. -/
theorem valuation_z (hn : ‖n‖ ≤ 1) : P.z.valuation = (P.depth : ℤ) := by
  rw [z, commonRoot_val_div (neg_ne_zero.mpr P.x_ne_zero) (P.y_ne_zero hn),
    commonRoot_val_neg]
  obtain ⟨_, hx, hy⟩ := P.depth_spec hn
  omega

/-- Exact affine-to-formal chart equations, valid on every negative-depth point. -/
theorem chart (hn : ‖n‖ ≤ 1) :
    P.W = 1 - n ^ 2 * P.z ^ 4 * P.W ^ 2 ∧
      -1 / P.y = P.z ^ 3 * P.W ∧
      P.x = P.z⁻¹ ^ 2 * P.W⁻¹ := by
  have hx := P.x_ne_zero
  have hy := P.y_ne_zero hn
  have hw : P.W = 1 - (n / P.x)^2 := by
    dsimp [W]
    field_simp [hx]
    linear_combination P.equation
  refine ⟨?_, ?_, ?_⟩
  · have he : P.z^4 * P.W^2 = (1 / P.x)^2 := by
      dsimp [z, W]
      field_simp [hx, hy]
    rw [mul_assoc, he, hw]
    ring
  · dsimp [z, W]
    field_simp [hx, hy]
  · dsimp [z, W]
    field_simp [hx, hy]

/-- The correction factor is a dyadic unit. -/
theorem valuation_W (hn : ‖n‖ ≤ 1) : P.W.valuation = 0 := by
  rw [W, commonRoot_val_div (pow_ne_zero _ (P.y_ne_zero hn))
    (pow_ne_zero _ P.x_ne_zero), Padic.valuation_pow, Padic.valuation_pow]
  have he := P.valuation_equation hn
  norm_num
  omega

theorem norm_W (hn : ‖n‖ ≤ 1) : ‖P.W‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (P.W_ne_zero hn), P.valuation_W hn]
  norm_num

/-- Pointwise integral fourth-order correction in the formal chart.
This assertion concerns actual dyadic points and does not assume a formal logarithm. -/
theorem W_integral_correction (hn : ‖n‖ ≤ 1) :
    ∃ a : ℤ_[2], P.W = 1 + P.z ^ 4 * (a : ℚ_[2]) := by
  have ha : ‖-(n * P.W)^2‖ ≤ 1 := by
    rw [norm_neg, norm_pow, norm_mul, P.norm_W hn, mul_one]
    simpa using pow_le_pow_left₀ (norm_nonneg n) hn 2
  refine ⟨⟨-(n * P.W)^2, ha⟩, ?_⟩
  have he := (P.chart hn).1
  change P.W = 1 + P.z ^ 4 * -(n * P.W)^2
  linear_combination he

/-- The error has fourth-order size uniformly in the depth. -/
theorem norm_W_sub_one_le (hn : ‖n‖ ≤ 1) :
    ‖P.W - 1‖ ≤ ‖P.z‖ ^ 4 := by
  obtain ⟨a, ha⟩ := P.W_integral_correction hn
  rw [ha, add_sub_cancel_left, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) a.property

end CommonSourceDyadicPoint

/-- Embed a rational affine point into the actual dyadic chart. -/
def commonSourceDyadicOfRat (n : ℤ) (x y : ℚ)
    (he : y ^ 2 = x * (x - n) * (x + n))
    (hv : padicValRat 2 x ≤ -4) : CommonSourceDyadicPoint (n : ℚ_[2]) where
  x := x
  y := y
  equation := by exact_mod_cast he
  depth_bound := by simpa only [Padic.valuation_ratCast] using hv

/-- All three ordered Kummer factors of a rational point in the prescribed
neighbourhood are squares in `ℚ₂`. -/
theorem commonSourceDyadic_rational_local_squares (n : ℤ) (x y : ℚ)
    (he : y ^ 2 = x * (x - n) * (x + n))
    (hv : padicValRat 2 x ≤ -4) :
    IsSquare (x : ℚ_[2]) ∧ IsSquare ((x - n : ℚ) : ℚ_[2]) ∧
      IsSquare ((x + n : ℚ) : ℚ_[2]) := by
  have h := (commonSourceDyadicOfRat n x y he hv).local_squares
    (Padic.norm_int_le_one n)
  simpa only [commonSourceDyadicOfRat, Rat.cast_sub, Rat.cast_add, Rat.cast_intCast] using h

#print axioms CommonSourceDyadicPoint.local_squares
#print axioms CommonSourceDyadicPoint.depth_spec
#print axioms CommonSourceDyadicPoint.chart
#print axioms CommonSourceDyadicPoint.W_integral_correction
#print axioms commonSourceDyadic_rational_local_squares

end FourCorner
