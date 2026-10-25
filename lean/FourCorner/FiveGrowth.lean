import FourCorner.DenominatorBounds

set_option autoImplicit false

namespace FourCorner
namespace IntegralModel

/-- The strict analytic comparison from a nonzero signed sum having the exact
five-adic depth. The exponent in the conclusion is an integer, so negative
values of `h - 3*s` retain their intended meaning. -/
theorem five_growth_of_signed_depth_factorization (M : IntegralModel)
    {h s : ℕ} {m b c d : ℤ}
    (hdepth : 2*s < h) (hL : M.L = (5:ℤ)^h*m)
    (hb : b=M.A₁ ∨ b= -M.A₁) (hc : c=M.A₂ ∨ c= -M.A₂)
    (hd : d=M.A₃ ∨ d= -M.A₃)
    (hne : M.A₀-b-c+d ≠ 0)
    (hv : padicValInt 5 (M.A₀-b-c+d) = 2*h-3*s) :
    (5:ℝ)^((h:ℤ)-3*(s:ℤ)) < (2+Real.sqrt 2)/2*(m:ℝ) := by
  have hdiv : (5:ℤ)^(2*h-3*s) ∣ M.A₀-b-c+d := by
    rw [← hv]
    exact padicValInt_dvd _
  have hcop : IsCoprime (2:ℤ) (5:ℤ) := ⟨-2,1,by norm_num⟩
  have hdiv2 := (hcop.pow_right).mul_dvd (M.bounds_signed_sum_even hb hc hd) hdiv
  have habs : 2*(5:ℤ)^(2*h-3*s) ∣ |M.A₀-b-c+d| := by
    rcases le_total 0 (M.A₀-b-c+d) with ht | ht
    · simpa only [abs_of_nonneg ht] using hdiv2
    · simpa only [abs_of_nonpos ht] using dvd_neg.mpr hdiv2
  have hle : 2*(5:ℤ)^(2*h-3*s) ≤ |M.A₀-b-c+d| :=
    Int.le_of_dvd (abs_pos.mpr hne) habs
  have hleR : 2*(5:ℝ)^(2*h-3*s) ≤ ((|M.A₀-b-c+d|:ℤ):ℝ) := by
    exact_mod_cast hle
  have hbound := hleR.trans_lt (M.bounds_signed_sum_lt hb hc hd)
  have hnat : 3*s ≤ 2*h := by omega
  have hexp : ((2*h-3*s:ℕ):ℤ) = (h:ℤ) + ((h:ℤ)-3*(s:ℤ)) := by
    rw [Nat.cast_sub hnat]
    push_cast
    ring
  have hpow : (5:ℝ)^(2*h-3*s) = (5:ℝ)^h * (5:ℝ)^((h:ℤ)-3*(s:ℤ)) := by
    rw [← zpow_natCast, hexp, zpow_add₀ (by norm_num), zpow_natCast]
  have hLR : (M.L:ℝ) = (5:ℝ)^h*(m:ℝ) := by exact_mod_cast hL
  rw [hpow,hLR] at hbound
  have hp : 0 < (5:ℝ)^h := by positivity
  apply (mul_lt_mul_iff_right₀ hp).mp
  nlinarith only [hbound]

/-- The five-primary cofactor is an integer because the full valuation power
divides the side. -/
theorem five_side_factorization (M : IntegralModel) :
    M.L = (5:ℤ)^padicValInt 5 M.L *
      (M.L / (5:ℤ)^padicValInt 5 M.L) := by
  exact (Int.mul_ediv_cancel' (padicValInt_dvd (p:=5) M.L)).symm

/-- Analytic half of `prop:int:five-depth`, expressed using the actual
five-primary cofactor of the side and an actual signed sum of the radii. -/
theorem five_growth_of_signed_depth (M : IntegralModel)
    {s : ℕ} {b c d : ℤ}
    (hdepth : 2*s < padicValInt 5 M.L)
    (hb : b=M.A₁ ∨ b= -M.A₁) (hc : c=M.A₂ ∨ c= -M.A₂)
    (hd : d=M.A₃ ∨ d= -M.A₃)
    (hne : M.A₀-b-c+d ≠ 0)
    (hv : padicValInt 5 (M.A₀-b-c+d) = 2*padicValInt 5 M.L-3*s) :
    (5:ℝ)^((padicValInt 5 M.L:ℤ)-3*(s:ℤ)) <
      (2+Real.sqrt 2)/2*(M.L / (5:ℤ)^padicValInt 5 M.L : ℤ) := by
  exact M.five_growth_of_signed_depth_factorization hdepth M.five_side_factorization
    hb hc hd hne hv

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.five_growth_of_signed_depth
