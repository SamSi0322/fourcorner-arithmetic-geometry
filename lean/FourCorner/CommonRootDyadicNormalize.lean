import FourCorner.CommonRootPadicVal
import FourCorner.CommonRootDyadicScale
import FourCorner.CommonRootDyadicResidues
import FourCorner.CommonRootDyadicFrame
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace FourCorner

theorem commonDyadic_unit_val {x : ℚ_[2]} (hx : ‖x‖ = 1) :
    x ≠ 0 ∧ x.valuation = 0 := by
  have hn : x ≠ 0 := by intro h; simp [h] at hx
  refine ⟨hn, ?_⟩
  rw [Padic.norm_eq_zpow_neg_valuation hn] at hx
  have hh : (2 : ℝ) ^ (-x.valuation) = (2 : ℝ) ^ (0 : ℤ) := by simpa using hx
  have hv := (zpow_right_inj₀ (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)).mp hh
  omega

theorem commonDyadic_quarter_val {x : ℚ_[2]} (hx : x ≠ 0)
    (hn : ‖x‖ ≤ (1/4 : ℝ)) : 2 ≤ x.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation hx] at hn
  have h : (2 : ℝ) ^ (-x.valuation) ≤ (2 : ℝ) ^ (-2 : ℤ) := by
    rw [show (2 : ℝ) ^ (-2 : ℤ) = 1/4 by norm_num]
    exact hn
  have hh := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp h
  omega

theorem commonDyadic_first_difference {N X : ℚ_[2]} (hN : N ≠ 0)
    (hn : ‖N‖ ≤ (1/4 : ℝ)) (hX : ‖X‖ = 1) :
    N - 2*X ≠ 0 ∧ (N - 2*X).valuation = 1 := by
  obtain ⟨hx, hvx⟩ := commonDyadic_unit_val hX
  have hvn := commonDyadic_quarter_val hN hn
  have htwo : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hv2 : (2 : ℚ_[2]).valuation = 1 := Padic.valuation_p
  have hvm : (2*X).valuation = 1 := by rw [Padic.valuation_mul htwo hx, hv2, hvx]; norm_num
  have hne : N.valuation ≠ (2*X).valuation := by omega
  refine ⟨commonRoot_sub_ne_zero_of_val_ne hne, ?_⟩
  rw [commonRoot_val_sub_of_ne hN (mul_ne_zero htwo hx) hne, hvm]
  exact min_eq_right (by omega)

theorem commonDyadic_second_difference {N Y : ℚ_[2]}
    (hn : ‖N‖ ≤ (1/4 : ℝ)) (hy : ‖Y‖ ≤ (1/4 : ℝ)) :
    N - 2*Y = 0 ∨ 2 ≤ (N - 2*Y).valuation := by
  by_cases hz : N - 2*Y = 0
  · exact Or.inl hz
  refine Or.inr (commonDyadic_quarter_val hz ?_)
  have hm : ‖2*Y‖ ≤ (1/4 : ℝ) := by
    rw [norm_mul, show ‖(2:ℚ_[2])‖ = (1/2:ℝ) by simpa using (Padic.norm_p (p:=2))]
    linarith
  calc
    ‖N - 2*Y‖ ≤ max ‖N‖ ‖-(2*Y)‖ := by simpa only [sub_eq_add_neg] using Padic.nonarchimedean N (-(2*Y))
    _ ≤ (1/4 : ℝ) := by rw [norm_neg]; exact max_le hn hm

/-- Multiplying a square-distance relation by an integral scale bounds its
actual dyadic square root; no choice of residue-field roots is used. -/
theorem commonDyadic_scaled_root_integral {N x y r : ℚ_[2]}
    (hx : ‖N*x‖ ≤ 1) (hy : ‖N*y‖ ≤ 1) (hr : r^2=x^2+y^2) :
    ‖N*r‖ ≤ 1 := by
  have he : (N*r)^2=(N*x)^2+(N*y)^2 := by rw [mul_pow,hr]; ring
  have hxx : ‖(N*x)^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg (N*x)]
  have hyy : ‖(N*y)^2‖ ≤ 1 := by rw [norm_pow]; nlinarith [norm_nonneg (N*y)]
  have hrr : ‖N*r‖^2 ≤ 1 := by
    rw [← norm_pow,he]
    exact (Padic.nonarchimedean _ _).trans (max_le hxx hyy)
  nlinarith [norm_nonneg (N*r)]

/-- An oriented normalized configuration gives the explicit dyadic frame. -/
theorem commonDyadic_frame_of_oriented_norms
    (t N X Y A0 A1 A2 A3 : ℚ_[2]) (h : ℕ)
    (hN : N ≠ 0) (hvN : N.valuation = (h:ℤ))
    (hn : ‖N‖ ≤ (1/4:ℝ)) (hx : ‖X‖=1) (hy : ‖Y‖≤(1/4:ℝ))
    (ha0 : ‖A0‖=1) (ha1 : ‖A1‖=1) (ha2 : ‖A2‖=1) (ha3 : ‖A3‖=1)
    (h0 : A0^2=X^2+Y^2) (h1 : A1^2=(N-X)^2+Y^2)
    (h2 : A2^2=X^2+(N-Y)^2) (h3 : A3^2=(N-X)^2+(N-Y)^2)
    (ht : t=(A0*A3+A1*A2)/N^2) : Nonempty (CommonDyadicFrame t) := by
  obtain ⟨ha00,hva0⟩ := commonDyadic_unit_val ha0
  obtain ⟨ha10,hva1⟩ := commonDyadic_unit_val ha1
  obtain ⟨ha20,hva2⟩ := commonDyadic_unit_val ha2
  obtain ⟨ha30,hva3⟩ := commonDyadic_unit_val ha3
  obtain ⟨hu0,hvu⟩ := commonDyadic_first_difference hN hn hx
  have hh : 2≤h := by have := commonDyadic_quarter_val hN hn; omega
  exact ⟨{
    N:=N, X:=X, Y:=Y, A0:=A0, A1:=A1, A2:=A2, A3:=A3, h:=h,
    h_ge_two:=hh, N_ne_zero:=hN, valN:=hvN,
    valA0:=hva0, valA1:=hva1, valA2:=hva2, valA3:=hva3,
    A0_ne_zero:=ha00, A1_ne_zero:=ha10, A2_ne_zero:=ha20, A3_ne_zero:=ha30,
    sq0:=h0,sq1:=h1,sq2:=h2,sq3:=h3,t_eq:=ht,
    U_ne_zero:=hu0,valU:=hvu,V_case:=commonDyadic_second_difference hn hy }⟩

/-- Every actual dyadic four-distance configuration admits a common primitive
integral scale and an orientation with the required unit-coordinate pattern.
The radius products, and therefore their labelled return parameter, are unchanged
by the possible interchange of the two axes. -/
theorem commonRoot_dyadic_frame_of_four_squares (x y r0 r1 r2 r3 : ℚ_[2])
    (h0 : r0^2=x^2+y^2) (h1 : r1^2=(1-x)^2+y^2)
    (h2 : r2^2=x^2+(1-y)^2) (h3 : r3^2=(1-x)^2+(1-y)^2) :
    Nonempty (CommonDyadicFrame (r0*r3+r1*r2)) := by
  obtain ⟨h,hN,hNi,hXi,hYi,hprim⟩ := commonRoot_dyadic_primitive_scale x y
  let N : ℚ_[2] := 2^h
  let X : ℚ_[2] := N*x
  let Y : ℚ_[2] := N*y
  have hvN : N.valuation=(h:ℤ) := by
    dsimp [N]
    rw [Padic.valuation_pow, show (2:ℚ_[2]).valuation=1 from Padic.valuation_p]
    ring
  have hNX : ‖N*(1-x)‖≤1 := by
    rw [show N*(1-x)=N+(-X) by dsimp [X]; ring]
    exact (Padic.nonarchimedean _ _).trans (max_le hNi (by rw [norm_neg]; exact hXi))
  have hNY : ‖N*(1-y)‖≤1 := by
    rw [show N*(1-y)=N+(-Y) by dsimp [Y]; ring]
    exact (Padic.nonarchimedean _ _).trans (max_le hNi (by rw [norm_neg]; exact hYi))
  have ha0 := commonDyadic_scaled_root_integral hXi hYi h0
  have ha1 := commonDyadic_scaled_root_integral hNX hYi h1
  have ha2 := commonDyadic_scaled_root_integral hXi hNY h2
  have ha3 := commonDyadic_scaled_root_integral hNX hNY h3
  let Ni : ℤ_[2] := ⟨N,hNi⟩
  let Xi : ℤ_[2] := ⟨X,hXi⟩
  let Yi : ℤ_[2] := ⟨Y,hYi⟩
  let a0 : ℤ_[2] := ⟨N*r0,ha0⟩
  let a1 : ℤ_[2] := ⟨N*r1,ha1⟩
  let a2 : ℤ_[2] := ⟨N*r2,ha2⟩
  let a3 : ℤ_[2] := ⟨N*r3,ha3⟩
  have hs0 : (N*r0)^2=X^2+Y^2 := by dsimp [X,Y]; rw [mul_pow,h0]; ring
  have hs1 : (N*r1)^2=(N-X)^2+Y^2 := by dsimp [X,Y]; rw [mul_pow,h1]; ring
  have hs2 : (N*r2)^2=X^2+(N-Y)^2 := by dsimp [X,Y]; rw [mul_pow,h2]; ring
  have hs3 : (N*r3)^2=(N-X)^2+(N-Y)^2 := by dsimp [X,Y]; rw [mul_pow,h3]; ring
  have hi0 : a0^2=Xi^2+Yi^2 := by apply PadicInt.ext; exact hs0
  have hi1 : a1^2=(Ni-Xi)^2+Yi^2 := by apply PadicInt.ext; exact hs1
  have hi2 : a2^2=Xi^2+(Ni-Yi)^2 := by apply PadicInt.ext; exact hs2
  have hi3 : a3^2=(Ni-Xi)^2+(Ni-Yi)^2 := by apply PadicInt.ext; exact hs3
  obtain ⟨hn,hor,hua0,hua1,hua2,hua3⟩ :=
    common_root_dyadic_primitive_norms Ni Xi Yi a0 a1 a2 a3 hi0 hi1 hi2 hi3 hprim
  have ht : r0*r3+r1*r2=((N*r0)*(N*r3)+(N*r1)*(N*r2))/N^2 := by
    apply (eq_div_iff (pow_ne_zero 2 (show N ≠ 0 from hN))).mpr
    ring
  rcases hor with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact commonDyadic_frame_of_oriented_norms _ N X Y (N*r0) (N*r1) (N*r2) (N*r3)
      h hN hvN hn hx hy hua0 hua1 hua2 hua3 hs0 hs1 hs2 hs3 ht
  · apply commonDyadic_frame_of_oriented_norms _ N Y X (N*r0) (N*r2) (N*r1) (N*r3)
      h hN hvN hn hy hx hua0 hua2 hua1 hua3
    · simpa only [add_comm] using hs0
    · simpa only [add_comm] using hs2
    · simpa only [add_comm] using hs1
    · simpa only [add_comm] using hs3
    · simpa only [mul_comm] using ht

#print axioms commonDyadic_unit_val
#print axioms commonDyadic_quarter_val
#print axioms commonDyadic_first_difference
#print axioms commonDyadic_second_difference
#print axioms commonDyadic_scaled_root_integral
#print axioms commonDyadic_frame_of_oriented_norms
#print axioms commonRoot_dyadic_frame_of_four_squares

end FourCorner
