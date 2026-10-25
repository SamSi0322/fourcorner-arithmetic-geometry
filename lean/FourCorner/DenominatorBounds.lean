import FourCorner.DenominatorBoundsArithmetic
import FourCorner.DenominatorBoundsReal

set_option autoImplicit false
namespace FourCorner
namespace IntegralModel

/-- Any choice of signs is bounded by the true sum of the four radii. -/
theorem bounds_signed_sum_lt (M : IntegralModel) {b c d : ℤ}
    (hb:b=M.A₁ ∨ b= -M.A₁) (hc:c=M.A₂ ∨ c= -M.A₂) (hd:d=M.A₃ ∨ d= -M.A₃) :
    ((|M.A₀-b-c+d| : ℤ) : ℝ) < (2+Real.sqrt 2)*(M.L:ℝ) := by
  have h : |M.A₀-b-c+d| ≤ M.A₀+M.A₁+M.A₂+M.A₃ := by
    have h0 := M.A₀_pos
    have h1 := M.A₁_pos
    have h2 := M.A₂_pos
    have h3 := M.A₃_pos
    apply abs_le.mpr
    rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;> rcases hd with rfl|rfl <;> constructor <;> omega
  have hr : ((|M.A₀-b-c+d|:ℤ):ℝ) ≤ (M.A₀:ℝ)+M.A₁+M.A₂+M.A₃ := by exact_mod_cast h
  exact hr.trans_lt M.radius_sum_lt

private theorem divisor_le_abs {D T : ℤ} (hT : T ≠ 0) (hd : D∣T) : D≤|T| := by
  have hda : D ∣ |T| := by
    rcases le_total 0 T with h | h
    · simpa only [abs_of_nonneg h] using hd
    · simpa only [abs_of_nonpos h] using dvd_neg.mpr hd
  exact Int.le_of_dvd (abs_pos.mpr hT) hda

/-- The complete dyadic prime power, without a valuation cutoff. -/
theorem two_prime_power_comparison (M : IntegralModel) :
    ((2:ℝ)^padicValInt 2 M.L)^2 < (2+Real.sqrt 2)/4*(M.L:ℝ) := by
  obtain ⟨b,c,d,hb,hc,hd,hne,hv⟩ := M.bounds_two_signed_value
  have hcoord := M.bounds_two_coordinate_depth
  have hdiv : (2:ℤ)^(2*padicValInt 2 M.L+2)∣M.A₀-b-c+d :=
    (padicValInt_dvd_iff (p:=2) _ _).mpr (Or.inr (by omega))
  have hle := divisor_le_abs hne hdiv
  have hleR : (2:ℝ)^(2*padicValInt 2 M.L+2) ≤ ((|M.A₀-b-c+d|:ℤ):ℝ) := by
    exact_mod_cast hle
  have h := hleR.trans_lt (M.bounds_signed_sum_lt hb hc hd)
  have hp : (2:ℝ)^(2*padicValInt 2 M.L+2)=4*((2:ℝ)^padicValInt 2 M.L)^2 := by
    rw [pow_add,Nat.mul_comm 2 (padicValInt 2 M.L),pow_mul]
    norm_num
    ring
  rw [hp] at h
  nlinarith

/-- Every odd prime dividing the side and a coordinate obeys the full
prime-power comparison in thm:int:prime-comparisons. -/
theorem odd_prime_power_comparison (M : IntegralModel) {p : ℕ}
    (hp:p.Prime) (hp2:p≠2) (hL:(p:ℤ)∣M.L) (hXY:(p:ℤ)∣M.X*M.Y) :
    ((p:ℝ)^padicValInt p M.L)^2 < (2+Real.sqrt 2)/(2*p)*(M.L:ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b,c,d,hb,hc,hd,hne,hv⟩ := M.bounds_odd_signed_value hp hp2 hL hXY
  have hcoord := M.bounds_odd_coordinate_depth hp hL hXY
  have hdiv : (p:ℤ)^(2*padicValInt p M.L+1)∣M.A₀-b-c+d :=
    (padicValInt_dvd_iff (p:=p) _ _).mpr (Or.inr (by omega))
  have hcop : IsCoprime (2:ℤ) (p:ℤ) :=
    ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).isCoprime
  have hdiv2 := (hcop.pow_right).mul_dvd (M.bounds_signed_sum_even hb hc hd) hdiv
  have hle := divisor_le_abs hne hdiv2
  have hleR : 2*(p:ℝ)^(2*padicValInt p M.L+1) ≤ ((|M.A₀-b-c+d|:ℤ):ℝ) := by
    exact_mod_cast hle
  have h := hleR.trans_lt (M.bounds_signed_sum_lt hb hc hd)
  have hpow : (p:ℝ)^(2*padicValInt p M.L+1)=((p:ℝ)^padicValInt p M.L)^2*p := by
    rw [pow_succ,Nat.mul_comm 2 (padicValInt p M.L),pow_mul]
  rw [hpow] at h
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hr : ((p:ℝ)^padicValInt p M.L)^2 < ((2+Real.sqrt 2)*(M.L:ℝ))/(2*p) := by
    apply (lt_div_iff₀ (by positivity : (0:ℝ)<2*p)).mpr
    nlinarith only [h]
  convert hr using 1 <;> ring

/-- The 3-primary instance is unconditional for the primitive four-corner model. -/
theorem three_prime_power_comparison (M : IntegralModel) :
    ((3:ℝ)^padicValInt 3 M.L)^2 < (2+Real.sqrt 2)/6*(M.L:ℝ) := by
  have hL : (3:ℤ)∣M.L := Int.dvd_of_emod_eq_zero M.three_divides_L
  have hXY : (3:ℤ)∣M.X*M.Y := by
    rcases M.coordinate_three_pattern with ⟨hx,_⟩|⟨hy,_⟩
    · exact dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hx) _
    · exact dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero hy) _
  convert M.odd_prime_power_comparison Nat.prime_three (by decide) hL hXY using 1 <;> norm_num

/-- Manuscript thm:int:prime-comparisons, with all hypotheses discharged
except the explicit odd-prime condition in its statement. -/
theorem prime_power_comparisons (M : IntegralModel) :
    ((2:ℝ)^padicValInt 2 M.L)^2 < (2+Real.sqrt 2)/4*(M.L:ℝ) ∧
    ((3:ℝ)^padicValInt 3 M.L)^2 < (2+Real.sqrt 2)/6*(M.L:ℝ) ∧
    (∀ p:ℕ, p.Prime → p≠2 → (p:ℤ)∣M.L → (p:ℤ)∣M.X*M.Y →
      ((p:ℝ)^padicValInt p M.L)^2 < (2+Real.sqrt 2)/(2*p)*(M.L:ℝ)) :=
  ⟨M.two_prime_power_comparison,M.three_prime_power_comparison,
    fun _ hp hp2 hL hXY => M.odd_prime_power_comparison hp hp2 hL hXY⟩

end IntegralModel
end FourCorner
#print axioms FourCorner.IntegralModel.prime_power_comparisons
