import FourCorner.DenominatorBounds
import FourCorner.DenominatorBoundsSmooth

set_option autoImplicit false
namespace FourCorner
namespace IntegralModel

private theorem bounds_value_pow {p:ℕ} (hp:p.Prime) (a:ℤ) (n:ℕ) :
    padicValInt p (a^n)=n*padicValInt p a := by
  letI : Fact p.Prime := ⟨hp⟩
  simp only [padicValInt,Int.natAbs_pow,padicValNat.pow]

/-- No actual primitive denominator is supported only on 2 and 3. -/
theorem no_two_three_power (M : IntegralModel) (a b:ℕ)
    (hL:M.L=(2:ℤ)^a*(3:ℤ)^b) : False := by
  have h23 : padicValInt 2 (3:ℤ)=0 := padicValInt.eq_zero_of_not_dvd (by norm_num)
  have h32 : padicValInt 3 (2:ℤ)=0 := padicValInt.eq_zero_of_not_dvd (by norm_num)
  have h22 : padicValInt 2 (2:ℤ)=1 := padicValInt_self (p:=2)
  have h33 : padicValInt 3 (3:ℤ)=1 := padicValInt_self (p:=3)
  have hv2 : padicValInt 2 M.L=a := by
    rw [hL,padicValInt.mul (pow_ne_zero a (by norm_num)) (pow_ne_zero b (by norm_num)),
      bounds_value_pow Nat.prime_two,bounds_value_pow Nat.prime_two,h22,h23]
    omega
  have hv3 : padicValInt 3 M.L=b := by
    rw [hL,padicValInt.mul (pow_ne_zero a (by norm_num)) (pow_ne_zero b (by norm_num)),
      bounds_value_pow Nat.prime_three,bounds_value_pow Nat.prime_three,h32,h33]
    omega
  have h2 := M.two_prime_power_comparison
  have h3 := M.three_prime_power_comparison
  rw [hv2] at h2
  rw [hv3] at h3
  have hLR : (0:ℝ)<M.L := by exact_mod_cast M.L_pos
  have hLeq : (M.L:ℝ)=(2:ℝ)^a*(3:ℝ)^b := by exact_mod_cast hL
  have hK : (0:ℝ)<(2:ℝ)^a := pow_pos (by norm_num) _
  have hP : (0:ℝ)<(3:ℝ)^b := pow_pos (by norm_num) _
  have hsqrt := Real.sqrt_nonneg (2:ℝ)
  have hsquare := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hdpos : (0:ℝ)<(2+Real.sqrt 2)/4*(M.L:ℝ) := by positivity
  have hm := (mul_lt_mul_of_pos_right h2 (sq_pos_of_pos hP)).trans
    (mul_lt_mul_of_pos_left h3 hdpos)
  have heq : ((2:ℝ)^a)^2*((3:ℝ)^b)^2=(M.L:ℝ)^2 := by rw [hLeq]; ring
  rw [heq] at hm
  have hbound : (2+Real.sqrt 2)^2 < (24:ℝ) := by nlinarith
  have hmul := mul_pos (sub_pos.mpr hbound) (sq_pos_of_pos hLR)
  nlinarith only [hm,hmul]

/-- Manuscript cor:int:six-smooth: an actual prime at least five divides
its least primitive coordinate denominator. -/
theorem exists_prime_ge_five_dvd_L (M : IntegralModel) :
    ∃ p:ℕ, p.Prime ∧ (p:ℤ)∣M.L ∧ 5≤p := by
  have hnot : ¬ ∃ a b:ℕ, M.L.natAbs=2^a*3^b := by
    rintro ⟨a,b,h⟩
    apply M.no_two_three_power a b
    have hi := congrArg (fun n:ℕ => (n:ℤ)) h
    push_cast at hi
    rw [abs_of_pos M.L_pos] at hi
    exact hi
  obtain ⟨p,hp,hdiv,hp5⟩ := exists_large_prime_of_not_two_three M.L.natAbs
    (Int.natAbs_pos.mpr (ne_of_gt M.L_pos)) hnot
  exact ⟨p,hp,Int.natCast_dvd.mpr hdiv,hp5⟩

end IntegralModel

/-- The least common coordinate denominator in the original rational problem
has a prime divisor at least five. -/
theorem strictPoint_denominator_large_prime {x y r₀ r₁ r₂ r₃:ℚ}
    (h : StrictPoint x y r₀ r₁ r₂ r₃) :
    ∃ p:ℕ, p.Prime ∧ p∣Nat.lcm x.den y.den ∧ 5≤p := by
  obtain ⟨M,hL,_,_,_,_,_,_⟩ := strictPoint_integralNormalization h
  obtain ⟨p,hp,hd,h5⟩ := M.exists_prime_ge_five_dvd_L
  rw [hL] at hd
  exact ⟨p,hp,Int.natCast_dvd_natCast.mp hd,h5⟩

end FourCorner
#print axioms FourCorner.IntegralModel.no_two_three_power

#print axioms FourCorner.IntegralModel.exists_prime_ge_five_dvd_L

#print axioms FourCorner.strictPoint_denominator_large_prime
