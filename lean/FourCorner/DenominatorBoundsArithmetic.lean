import FourCorner.DenominatorBoundsValuation
import FourCorner.PrimitiveCongruences
import FourCorner.IntegralNormalization
import FourCorner.FermatSymmetry
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
namespace FourCorner
namespace IntegralModel

theorem bounds_horizontal_ne_zero (M : IntegralModel) : M.L - 2*M.X ≠ 0 := by
  intro hz
  have h := strict_point_not_vertical_midline M.toStrictPoint
  apply h
  have hL : (M.L : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt M.L_pos
  have hh : (M.L : ℚ) - 2*M.X = 0 := by exact_mod_cast hz
  field_simp
  linarith

theorem bounds_vertical_ne_zero (M : IntegralModel) : M.L - 2*M.Y ≠ 0 := by
  intro hz
  have h := strict_point_not_horizontal_midline M.toStrictPoint
  apply h
  have hL : (M.L : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt M.L_pos
  have hh : (M.L : ℚ) - 2*M.Y = 0 := by exact_mod_cast hz
  field_simp
  linarith

theorem bounds_flag (M : IntegralModel) : M.A₀^2 + M.A₃^2 = M.A₁^2 + M.A₂^2 := by
  linear_combination M.sq₀ + M.sq₃ - M.sq₁ - M.sq₂

theorem bounds_horizontal_difference (M : IntegralModel) :
    M.A₁^2-M.A₀^2=M.L*(M.L-2*M.X) := by rw [M.sq₁,M.sq₀]; ring

theorem bounds_vertical_difference (M : IntegralModel) :
    M.A₂^2-M.A₀^2=M.L*(M.L-2*M.Y) := by rw [M.sq₂,M.sq₀]; ring

theorem bounds_diagonal_difference (M : IntegralModel) :
    M.A₃^2-M.A₀^2=M.L*(2*(M.L-M.X-M.Y)) := by rw [M.sq₃,M.sq₀]; ring

theorem bounds_radii_odd (M : IntegralModel) :
    ¬(2:ℤ)∣M.A₀ ∧ ¬(2:ℤ)∣M.A₁ ∧ ¬(2:ℤ)∣M.A₂ ∧ ¬(2:ℤ)∣M.A₃ := by
  obtain ⟨_,_,h0,h1,h2,h3⟩ := M.four_divides_L_and_orientation
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- The odd prime at which a coordinate vanishes cannot divide any radius. -/
theorem bounds_origin_unit (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (hL : (p:ℤ)∣M.L) (hXY : (p:ℤ)∣M.X*M.Y) : ¬ (p:ℤ)∣M.A₀ := by
  intro hA
  have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_or_dvd hXY with hX | hY
  · have hY2 : (p:ℤ) ∣ M.Y^2 := by
      have hh := dvd_sub (dvd_pow hA (by decide : 2≠0)) (dvd_pow hX (by decide : 2≠0))
      rw [M.sq₀] at hh
      simpa using hh
    have hY : (p:ℤ)∣M.Y := hpZ.dvd_of_dvd_pow hY2
    exact hp.ne_one (M.common_divisor_eq_one hX hY hL)
  · have hX2 : (p:ℤ) ∣ M.X^2 := by
      have hh := dvd_sub (dvd_pow hA (by decide : 2≠0)) (dvd_pow hY (by decide : 2≠0))
      rw [M.sq₀] at hh
      simpa using hh
    have hX : (p:ℤ)∣M.X := hpZ.dvd_of_dvd_pow hX2
    exact hp.ne_one (M.common_divisor_eq_one hX hY hL)

/-- An actual choice of signs realizes the full odd-prime depth. -/
theorem bounds_odd_signed_value (M : IntegralModel) {p : ℕ}
    (hp : p.Prime) (hp2 : p≠2) (hL : (p:ℤ)∣M.L) (hXY : (p:ℤ)∣M.X*M.Y) :
    ∃ b c d : ℤ, (b=M.A₁ ∨ b= -M.A₁) ∧ (c=M.A₂ ∨ c= -M.A₂) ∧
      (d=M.A₃ ∨ d= -M.A₃) ∧ M.A₀-b-c+d≠0 ∧
      padicValInt p (M.A₀-b-c+d) = 2*padicValInt p M.L +
        padicValInt p (M.L-2*M.X) + padicValInt p (M.L-2*M.Y) := by
  obtain ⟨b,c,d,hb,hc,hd,_,_,_,hne,hv⟩ := BoundsValuation.odd_value_from_differences hp hp2
    M.A₀ M.A₁ M.A₂ M.A₃ M.L (M.L-2*M.X) (M.L-2*M.Y) (2*(M.L-M.X-M.Y))
    (ne_of_gt M.L_pos) M.bounds_horizontal_ne_zero M.bounds_vertical_ne_zero
    hL (M.bounds_origin_unit hp hL hXY) M.bounds_flag M.bounds_horizontal_difference
    M.bounds_vertical_difference M.bounds_diagonal_difference
  exact ⟨b,c,d,hb,hc,hd,hne,hv⟩

/-- At 2 the same sign construction retains every valuation depth. -/
theorem bounds_two_signed_value (M : IntegralModel) :
    ∃ b c d : ℤ, (b=M.A₁ ∨ b= -M.A₁) ∧ (c=M.A₂ ∨ c= -M.A₂) ∧
      (d=M.A₃ ∨ d= -M.A₃) ∧ M.A₀-b-c+d≠0 ∧
      padicValInt 2 (M.A₀-b-c+d)+2 = 2*padicValInt 2 M.L +
        padicValInt 2 (M.L-2*M.X) + padicValInt 2 (M.L-2*M.Y) := by
  have he := M.basic_mod_four.1
  obtain ⟨h0,h1,h2,h3⟩ := M.bounds_radii_odd
  obtain ⟨b,c,d,hb,hc,hd,_,_,_,hne,hv⟩ := BoundsValuation.two_value_from_differences
    M.A₀ M.A₁ M.A₂ M.A₃ M.L (M.L-2*M.X) (M.L-2*M.Y) (2*(M.L-M.X-M.Y))
    (ne_of_gt M.L_pos) M.bounds_horizontal_ne_zero M.bounds_vertical_ne_zero
    h0 h1 h2 h3 (by omega) (by omega) (dvd_mul_right _ _) M.bounds_flag
    M.bounds_horizontal_difference M.bounds_vertical_difference M.bounds_diagonal_difference
  exact ⟨b,c,d,hb,hc,hd,hne,hv⟩

theorem bounds_two_coordinate_depth (M : IntegralModel) :
    4 ≤ padicValInt 2 (M.L-2*M.X) + padicValInt 2 (M.L-2*M.Y) := by
  have h8 := M.eight_divides_L
  have hx2 : (2:ℤ)∣M.L-2*M.X := by omega
  have hy2 : (2:ℤ)∣M.L-2*M.Y := by omega
  have hxv := BoundsValuation.padic_pos_of_dvd Nat.prime_two M.bounds_horizontal_ne_zero hx2
  have hyv := BoundsValuation.padic_pos_of_dvd Nat.prime_two M.bounds_vertical_ne_zero hy2
  obtain ⟨_,hor,_⟩ := M.four_divides_L_and_orientation
  rcases hor with ⟨_,hy⟩ | ⟨_,hx⟩
  · have hd : (2:ℤ)^3 ∣ M.L-2*M.Y := by norm_num; omega
    have hv := ((padicValInt_dvd_iff (p:=2) 3 _).mp hd).resolve_left M.bounds_vertical_ne_zero
    omega
  · have hd : (2:ℤ)^3 ∣ M.L-2*M.X := by norm_num; omega
    have hv := ((padicValInt_dvd_iff (p:=2) 3 _).mp hd).resolve_left M.bounds_horizontal_ne_zero
    omega

theorem bounds_odd_coordinate_depth (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (hL : (p:ℤ)∣M.L) (hXY : (p:ℤ)∣M.X*M.Y) :
    1 ≤ padicValInt p (M.L-2*M.X)+padicValInt p (M.L-2*M.Y) := by
  have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_or_dvd hXY with hx | hy
  · have hd : (p:ℤ)∣M.L-2*M.X := dvd_sub hL (dvd_mul_of_dvd_right hx _)
    have hv := BoundsValuation.padic_pos_of_dvd hp M.bounds_horizontal_ne_zero hd
    omega
  · have hd : (p:ℤ)∣M.L-2*M.Y := dvd_sub hL (dvd_mul_of_dvd_right hy _)
    have hv := BoundsValuation.padic_pos_of_dvd hp M.bounds_vertical_ne_zero hd
    omega

theorem bounds_signed_sum_even (M : IntegralModel) {b c d : ℤ}
    (hb:b=M.A₁ ∨ b= -M.A₁) (hc:c=M.A₂ ∨ c= -M.A₂) (hd:d=M.A₃ ∨ d= -M.A₃) :
    (2:ℤ)∣M.A₀-b-c+d := by
  obtain ⟨_,_,h0,h1,h2,h3⟩ := M.four_divides_L_and_orientation
  rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> rcases hd with rfl|rfl <;> omega

end IntegralModel
end FourCorner
#print axioms FourCorner.IntegralModel.bounds_odd_signed_value
#print axioms FourCorner.IntegralModel.bounds_two_signed_value
#print axioms FourCorner.IntegralModel.bounds_two_coordinate_depth
