import ThetaCoverClassPortable.FourCorner.ThetaBitangentCore
import ThetaCoverClassPortable.FourCorner.ThetaBitangentAxisIdentities
import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner

variable {K : Type*} [Field K] [CharZero K]

/-- If an even binary quartic has nonzero constant coefficient and is a
nonzero scalar times the square of a separable binary quadratic, the middle
quadratic coefficient vanishes. This also excludes a degenerate leading term. -/
theorem theta_even_square_coefficients {A4 A2 A0 k a b c : K}
    (hk : k ≠ 0) (hd : b^2-4*a*c ≠ 0) (hA0 : A0 ≠ 0)
    (h4 : A4=k*a^2) (h2 : A2=k*(b^2+2*a*c))
    (h1 : 0=2*k*b*c) (h0 : A0=k*c^2) :
    b=0 ∧ a≠0 ∧ c≠0 ∧ A4≠0 ∧ A2^2=4*A4*A0 := by
  have hc : c≠0 := by intro hz; apply hA0; simpa [hz] using h0
  have h2k : (2:K)*k≠0 := mul_ne_zero (by norm_num) hk
  have hb : b=0 := (mul_eq_zero.mp ((mul_eq_zero.mp h1.symm).resolve_right hc)).resolve_left h2k
  have ha : a≠0 := by intro hz; apply hd; simp [hb,hz]
  refine ⟨hb,ha,hc,?_,?_⟩
  · rw [h4]
    exact mul_ne_zero hk (pow_ne_zero 2 ha)
  · rw [h2,h4,h0,hb]
    ring

/-- Conversely, the discriminant equation for an even quartic with nonzero
constant and middle coefficients provides a literal separable quadratic square. -/
theorem theta_even_square_coefficients_converse {A4 A2 A0 : K}
    (hA0 : A0≠0) (hA2 : A2≠0) (hd : A2^2=4*A4*A0) :
    ∃ k a b c : K, k≠0 ∧ b^2-4*a*c≠0 ∧
      A4=k*a^2 ∧ 0=2*k*a*b ∧ A2=k*(b^2+2*a*c) ∧
      0=2*k*b*c ∧ A0=k*c^2 := by
  refine ⟨A0,A2/(2*A0),0,1,hA0,?_,?_,?_,?_,?_,?_⟩
  · simp only [zero_pow (by decide : (2:ℕ)≠0), zero_sub, mul_one, neg_ne_zero]
    exact mul_ne_zero (by norm_num) (div_ne_zero hA2 (mul_ne_zero (by norm_num) hA0))
  · field_simp
    linear_combination -hd
  · ring
  · field_simp
    ring
  · ring
  · ring

/-- Reversing the binary coordinates preserves the literal square condition. -/
theorem theta_square_coefficients_reverse {A4 A3 A2 A1 A0 : K}
    (h : ThetaSquareCoefficients A4 A3 A2 A1 A0) :
    ThetaSquareCoefficients A0 A1 A2 A3 A4 := by
  obtain ⟨k,a,b,c,hk,hd,h4,h3,h2,h1,h0⟩ := h
  refine ⟨k,c,b,a,hk,?_,h0,?_,?_,?_,h4⟩
  · convert hd using 1 <;> ring
  · rw [h1]; ring
  · rw [h2]; ring
  · rw [h3]; ring

theorem theta_even_square_discriminant {A4 A2 A0 : K}
    (hA0 : A0≠0) (h : ThetaSquareCoefficients A4 0 A2 0 A0) :
    A4≠0 ∧ A2^2=4*A4*A0 := by
  obtain ⟨k,a,b,c,hk,hd,h4,h3,h2,h1,h0⟩ := h
  obtain ⟨hb,ha,hc,hn,he⟩ := theta_even_square_coefficients hk hd hA0 h4 h2 h1 h0
  exact ⟨hn,he⟩

/-- Complete even-quartic coefficient criterion, retaining separability. -/
theorem theta_even_square_iff {A4 A2 A0 : K} (hA0 : A0≠0) :
    ThetaSquareCoefficients A4 0 A2 0 A0 ↔
      A2≠0 ∧ A2^2=4*A4*A0 := by
  constructor
  · intro h
    obtain ⟨hA4,hd⟩ := theta_even_square_discriminant hA0 h
    refine ⟨?_,hd⟩
    intro hz
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at hd
    exact (mul_ne_zero (mul_ne_zero (by norm_num : (4:K)≠0) hA4) hA0) hd.symm
  · rintro ⟨hA2,hd⟩
    exact theta_even_square_coefficients_converse hA0 hA2 hd

/-- All axis-parallel affine restrictions, including the leading-zero case. -/
theorem theta_axis_coefficients_iff (u : K) :
    ThetaSquareCoefficients
      (9801-39592*u^2+39984*u^4) 0 (19598-39592*u^2) 0 9801 ↔
      u^2=1/2 ∨ u^2=50 := by
  constructor
  · intro h
    obtain ⟨hn,hd⟩ := theta_even_square_discriminant (by norm_num : (9801:K)≠0) h
    apply theta_axis_square_values
    linear_combination hd
  · intro h
    apply (theta_even_square_iff (by norm_num : (9801:K)≠0)).mpr
    refine ⟨?_,?_⟩
    · rcases h with h | h <;> rw [h] <;> norm_num
    · have hz : (19598-39592*u^2)^2-4*9801*(9801-39592*u^2+39984*u^4)=0 := by
        rw [theta_axis_discriminant_factor]
        rcases h with h | h <;> rw [h] <;> norm_num
      linear_combination hz

/-- Complete vertical restriction criterion. -/
theorem theta_vertical_coefficients_iff (t : K) :
    ThetaSquareCoefficients (9801*(t^4+1)+19598*t^2) 0
      (-39592*(t^2+1)) 0 39984 ↔ t^4-100*t^2+1=0 := by
  constructor
  · intro h
    obtain ⟨hn,hd⟩ := theta_even_square_discriminant (by norm_num : (39984:K)≠0) h
    apply theta_vertical_square_values
    linear_combination hd
  · intro h
    apply (theta_even_square_iff (by norm_num : (39984:K)≠0)).mpr
    refine ⟨?_,?_⟩
    · apply mul_ne_zero (by norm_num : (-39592:K)≠0)
      intro he
      have hfac : t^4-100*t^2+1=(t^2+1)*(t^2-101)+102 := by ring
      rw [hfac,he] at h
      norm_num at h
    · have hz : (-39592*(t^2+1))^2-4*39984*(9801*(t^4+1)+19598*t^2)=0 := by
        rw [theta_vertical_discriminant_factor,h,mul_zero]
      linear_combination hz

/-- The actual lines Z=uX are bitangent exactly at the two square values. -/
theorem theta_affine_x_axis_bitangent_iff (u : K) :
    IsThetaBitangent (.affine u 0) ↔ u^2=1/2 ∨ u^2=50 := by
  rw [theta_affine_bitangent_iff]
  simpa [thetaA4,thetaA3,thetaA2,thetaA1,thetaA0] using theta_axis_coefficients_iff u

/-- The actual lines Z=uY obey the same complete criterion. -/
theorem theta_affine_y_axis_bitangent_iff (u : K) :
    IsThetaBitangent (.affine 0 u) ↔ u^2=1/2 ∨ u^2=50 := by
  rw [theta_affine_bitangent_iff]
  constructor
  · intro h
    apply (theta_axis_coefficients_iff u).mp
    simpa [thetaA4,thetaA3,thetaA2,thetaA1,thetaA0] using theta_square_coefficients_reverse h
  · intro h
    have hh := theta_square_coefficients_reverse ((theta_axis_coefficients_iff u).mpr h)
    simpa [thetaA4,thetaA3,thetaA2,thetaA1,thetaA0] using hh

/-- The actual vertical lines X=tY have the stated reciprocal quartic parameter. -/
theorem theta_vertical_line_bitangent_iff (t : K) :
    IsThetaBitangent (.vertical t) ↔ t^4-100*t^2+1=0 := by
  rw [theta_vertical_bitangent_iff,theta_vertical_coefficients_iff]

/-- The projective line Y=0 does not satisfy the contact-square condition. -/
theorem theta_yzero_not_bitangent : ¬ IsThetaBitangent (ThetaLine.yzero : ThetaLine K) := by
  rw [theta_yzero_bitangent_iff]
  intro h
  obtain ⟨hn,hd⟩ := theta_even_square_discriminant (by norm_num : (39984:K)≠0) h
  norm_num at hd

/-- The remaining two coordinate axes are likewise excluded. -/
theorem theta_coordinate_axes_not_bitangent :
    ¬ IsThetaBitangent (ThetaLine.affine (0:K) 0) ∧
      ¬ IsThetaBitangent (ThetaLine.vertical (0:K)) := by
  rw [theta_affine_x_axis_bitangent_iff,theta_vertical_line_bitangent_iff]
  norm_num

#print axioms theta_even_square_coefficients
#print axioms theta_even_square_coefficients_converse
#print axioms theta_square_coefficients_reverse
#print axioms theta_even_square_discriminant
#print axioms theta_even_square_iff
#print axioms theta_axis_coefficients_iff
#print axioms theta_vertical_coefficients_iff
#print axioms theta_affine_x_axis_bitangent_iff
#print axioms theta_affine_y_axis_bitangent_iff
#print axioms theta_vertical_line_bitangent_iff
#print axioms theta_yzero_not_bitangent
#print axioms theta_coordinate_axes_not_bitangent

end FourCorner
