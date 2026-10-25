import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Int.Basic

set_option autoImplicit false

namespace FourCorner
namespace BoundsValuation

theorem lf_identity (A b c d : ℤ)
    (h : A ^ 2 + d ^ 2 = b ^ 2 + c ^ 2) :
    (A - b - c + d) * (b + c + d - A) =
      -2 * (b - A) * (c - A) := by
  linear_combination h

theorem signed_sq {a b : ℤ} (h : b = a ∨ b = -a) : b ^ 2 = a ^ 2 := by
  rcases h with rfl | rfl <;> ring

theorem prime_power_cancel_right {p n : ℕ} (hp : p.Prime)
    {x y : ℤ} (hy : ¬ (p : ℤ) ∣ y) (h : (p : ℤ) ^ n ∣ x * y) :
    (p : ℤ) ^ n ∣ x := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hx : x = 0
  · simp [hx]
  have hyn : y ≠ 0 := by
    intro hz
    apply hy
    simp [hz]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hyn
  have hv : n ≤ padicValInt p (x * y) :=
    ((padicValInt_dvd_iff n (x * y)).mp h).resolve_left hxy
  rw [padicValInt.mul hx hyn, padicValInt.eq_zero_of_not_dvd hy, add_zero] at hv
  exact (padicValInt_dvd_iff n x).mpr (Or.inr hv)

theorem odd_prime_not_dvd_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ (p : ℤ) ∣ (2 : ℤ) := by
  intro h
  have hn : p ∣ 2 := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hn)

theorem odd_prime_not_dvd_two_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : ℤ} (hA : ¬ (p : ℤ) ∣ A) : ¬ (p : ℤ) ∣ 2 * A := by
  intro h
  rcases Int.Prime.dvd_mul' hp h with h2 | ha
  · exact odd_prime_not_dvd_two hp hp2 h2
  · exact hA ha

/-- The sign and full prime-power congruence are constructed from the squared
congruence; the opposite sum is proved to be a local unit. -/
theorem odd_sign_choice {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A B : ℤ) (hA : ¬ (p : ℤ) ∣ A)
    (hsq : (p : ℤ) ^ n ∣ B ^ 2 - A ^ 2) :
    ∃ b : ℤ, (b = B ∨ b = -B) ∧
      (p : ℤ) ^ n ∣ b - A ∧ ¬ (p : ℤ) ∣ b + A := by
  have hprod : (p : ℤ) ^ n ∣ (B - A) * (B + A) := by
    convert hsq using 1 <;> ring
  by_cases hm : (p : ℤ) ∣ B - A
  · have hplus : ¬ (p : ℤ) ∣ B + A := by
      intro ht
      have htwo : (p : ℤ) ∣ 2 * A := by
        have he : (B + A) - (B - A) = 2 * A := by ring
        simpa only [he] using dvd_sub ht hm
      exact odd_prime_not_dvd_two_mul hp hp2 hA htwo
    exact ⟨B, Or.inl rfl, prime_power_cancel_right hp hplus hprod, hplus⟩
  · have hpow : (p : ℤ) ^ n ∣ B + A := by
      apply prime_power_cancel_right hp hm
      simpa [mul_comm] using hprod
    refine ⟨-B, Or.inr rfl, ?_, ?_⟩
    · have he : -(B + A) = -B - A := by ring
      simpa only [he] using dvd_neg.mpr hpow
    · intro ht
      apply hm
      have he : -(-B + A) = B - A := by ring
      simpa only [he] using dvd_neg.mpr ht

theorem prime_dvd_power_of_pos {p n : ℕ} (hn : 0 < n) :
    (p : ℤ) ∣ (p : ℤ) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ]
  exact dvd_mul_left _ _

theorem padic_pos_of_dvd {p : ℕ} (hp : p.Prime) {N : ℤ}
    (hN : N ≠ 0) (hd : (p : ℤ) ∣ N) : 0 < padicValInt p N := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd' : (p : ℤ) ^ 1 ∣ N := by simpa using hd
  have hv := ((padicValInt_dvd_iff 1 N).mp hd').resolve_left hN
  omega

theorem selected_F_unit {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 0 < n) {A b c d : ℤ} (hA : ¬ (p : ℤ) ∣ A)
    (hb : (p : ℤ) ^ n ∣ b - A)
    (hc : (p : ℤ) ^ n ∣ c - A)
    (hd : (p : ℤ) ^ n ∣ d - A) :
    ¬ (p : ℤ) ∣ b + c + d - A := by
  have hpw := prime_dvd_power_of_pos (p := p) hn
  have hsum : (p : ℤ) ∣ (b + c + d - A) - 2 * A := by
    have he : (b - A) + (c - A) + (d - A) = (b + c + d - A) - 2 * A := by ring
    simpa only [he] using dvd_add (dvd_add (hpw.trans hb) (hpw.trans hc)) (hpw.trans hd)
  intro h
  have htwo : (p : ℤ) ∣ 2 * A := by
    have he : (b + c + d - A) - ((b + c + d - A) - 2 * A) = 2 * A := by ring
    simpa only [he] using dvd_sub h hsum
  exact odd_prime_not_dvd_two_mul hp hp2 hA htwo

/-- The exact odd-prime valuation, derived from the actual quadratic differences.
The nonzero horizontal and vertical differences make every used valuation finite. -/
theorem odd_value_from_differences {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (A B C D N dx dy dz : ℤ)
    (hN : N ≠ 0) (hdx : dx ≠ 0) (hdy : dy ≠ 0)
    (hpN : (p : ℤ) ∣ N) (hpA : ¬ (p : ℤ) ∣ A)
    (hflag : A ^ 2 + D ^ 2 = B ^ 2 + C ^ 2)
    (hB : B ^ 2 - A ^ 2 = N * dx)
    (hC : C ^ 2 - A ^ 2 = N * dy)
    (hD : D ^ 2 - A ^ 2 = N * dz) :
    ∃ b c d : ℤ,
      (b = B ∨ b = -B) ∧ (c = C ∨ c = -C) ∧ (d = D ∨ d = -D) ∧
      (p : ℤ) ^ padicValInt p N ∣ b - A ∧
      (p : ℤ) ^ padicValInt p N ∣ c - A ∧
      (p : ℤ) ^ padicValInt p N ∣ d - A ∧
      A - b - c + d ≠ 0 ∧
      padicValInt p (A - b - c + d) =
        2 * padicValInt p N + padicValInt p dx + padicValInt p dy := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpow := padicValInt_dvd (p := p) N
  have hdivB : (p : ℤ) ^ padicValInt p N ∣ B ^ 2 - A ^ 2 := by
    rw [hB]
    exact dvd_mul_of_dvd_left hpow dx
  have hdivC : (p : ℤ) ^ padicValInt p N ∣ C ^ 2 - A ^ 2 := by
    rw [hC]
    exact dvd_mul_of_dvd_left hpow dy
  have hdivD : (p : ℤ) ^ padicValInt p N ∣ D ^ 2 - A ^ 2 := by
    rw [hD]
    exact dvd_mul_of_dvd_left hpow dz
  obtain ⟨b, hbsg, hb, hbunit⟩ := odd_sign_choice hp hp2 A B hpA hdivB
  obtain ⟨c, hcsg, hc, hcunit⟩ := odd_sign_choice hp hp2 A C hpA hdivC
  obtain ⟨d, hdsg, hd, _⟩ := odd_sign_choice hp hp2 A D hpA hdivD
  have hbsq := signed_sq hbsg
  have hcsq := signed_sq hcsg
  have hdsq := signed_sq hdsg
  have hbprod : (b - A) * (b + A) = N * dx := by
    linear_combination hbsq + hB
  have hcprod : (c - A) * (c + A) = N * dy := by
    linear_combination hcsq + hC
  have hbmn : b - A ≠ 0 := by
    intro h
    have := hbprod
    simp only [h, zero_mul] at this
    exact mul_ne_zero hN hdx this.symm
  have hcmn : c - A ≠ 0 := by
    intro h
    have := hcprod
    simp only [h, zero_mul] at this
    exact mul_ne_zero hN hdy this.symm
  have hbpn : b + A ≠ 0 := by
    intro h
    exact hbunit (by simp [h])
  have hcpn : c + A ≠ 0 := by
    intro h
    exact hcunit (by simp [h])
  have hFunit := selected_F_unit hp hp2 (padic_pos_of_dvd hp hN hpN) hpA hb hc hd
  have hFn : b + c + d - A ≠ 0 := by
    intro h
    exact hFunit (by simp [h])
  have hlf := lf_identity A b c d (by
    linear_combination hflag + hdsq - hbsq - hcsq)
  have hneg2 : (-2 : ℤ) ≠ 0 := by norm_num
  have hLn : A - b - c + d ≠ 0 := by
    intro h
    rw [h, zero_mul] at hlf
    exact mul_ne_zero (mul_ne_zero hneg2 hbmn) hcmn hlf.symm
  have hvb := congrArg (padicValInt p) hbprod
  rw [padicValInt.mul hbmn hbpn, padicValInt.mul hN hdx,
    padicValInt.eq_zero_of_not_dvd hbunit, add_zero] at hvb
  have hvc := congrArg (padicValInt p) hcprod
  rw [padicValInt.mul hcmn hcpn, padicValInt.mul hN hdy,
    padicValInt.eq_zero_of_not_dvd hcunit, add_zero] at hvc
  have hn2unit : ¬ (p : ℤ) ∣ (-2 : ℤ) := by
    intro h
    exact odd_prime_not_dvd_two hp hp2 (dvd_neg.mp h)
  have hvl := congrArg (padicValInt p) hlf
  rw [padicValInt.mul hLn hFn,
    padicValInt.mul (mul_ne_zero hneg2 hbmn) hcmn,
    padicValInt.mul hneg2 hbmn,
    padicValInt.eq_zero_of_not_dvd hFunit,
    padicValInt.eq_zero_of_not_dvd hn2unit] at hvl
  refine ⟨b, c, d, hbsg, hcsg, hdsg, hb, hc, hd, hLn, ?_⟩
  omega

theorem two_value_one {x : ℤ} (h2 : (2 : ℤ) ∣ x) (h4 : ¬ (4 : ℤ) ∣ x) :
    padicValInt 2 x = 1 := by
  have hx : x ≠ 0 := by
    intro h
    apply h4
    simp [h]
  have h2' : (2 : ℤ) ^ 1 ∣ x := by simpa using h2
  have hlo := ((padicValInt_dvd_iff 1 x).mp h2').resolve_left hx
  have hhi : ¬ 2 ≤ padicValInt 2 x := by
    intro h
    have hd := (padicValInt_dvd_iff 2 x).mpr (Or.inr h)
    norm_num at hd
    exact h4 hd
  exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge hhi)) hlo

theorem odd_sign_mod_four (A B : ℤ)
    (hA : ¬ (2 : ℤ) ∣ A) (hB : ¬ (2 : ℤ) ∣ B) :
    ∃ b : ℤ, (b = B ∨ b = -B) ∧ (4 : ℤ) ∣ b - A := by
  by_cases h : (4 : ℤ) ∣ B - A
  · exact ⟨B, Or.inl rfl, h⟩
  · refine ⟨-B, Or.inr rfl, ?_⟩
    omega

theorem mod_four_sum_value {A b : ℤ}
    (hA : ¬ (2 : ℤ) ∣ A) (hb : (4 : ℤ) ∣ b - A) :
    padicValInt 2 (b + A) = 1 := by
  apply two_value_one <;> omega

/-- At two the sign is first fixed modulo four; the square congruence
then promotes it to the full requested power, including zero differences. -/
theorem two_sign_choice {n : ℕ} (A B : ℤ)
    (hA : ¬ (2 : ℤ) ∣ A) (hB : ¬ (2 : ℤ) ∣ B)
    (hsq : (2 : ℤ) ^ (n + 1) ∣ B ^ 2 - A ^ 2) :
    ∃ b : ℤ, (b = B ∨ b = -B) ∧ (4 : ℤ) ∣ b - A ∧
      (2 : ℤ) ^ n ∣ b - A ∧ padicValInt 2 (b + A) = 1 := by
  obtain ⟨b, hbsg, hb4⟩ := odd_sign_mod_four A B hA hB
  have hvplus := mod_four_sum_value hA hb4
  refine ⟨b, hbsg, hb4, ?_, hvplus⟩
  by_cases hbm : b - A = 0
  · simp [hbm]
  have hbp : b + A ≠ 0 := by
    intro hz
    simp [hz] at hvplus
  have hbsq := signed_sq hbsg
  have hprod : (b - A) * (b + A) = B ^ 2 - A ^ 2 := by
    linear_combination hbsq
  have hprodne : B ^ 2 - A ^ 2 ≠ 0 := by
    rw [← hprod]
    exact mul_ne_zero hbm hbp
  have hv := ((padicValInt_dvd_iff (n + 1) (B ^ 2 - A ^ 2)).mp hsq).resolve_left hprodne
  rw [← hprod, padicValInt.mul hbm hbp, hvplus] at hv
  exact (padicValInt_dvd_iff n (b - A)).mpr (Or.inr (by omega))

theorem selected_F_two_value {A b c d : ℤ}
    (hA : ¬ (2 : ℤ) ∣ A)
    (hb : (4 : ℤ) ∣ b - A) (hc : (4 : ℤ) ∣ c - A)
    (hd : (4 : ℤ) ∣ d - A) :
    padicValInt 2 (b + c + d - A) = 1 := by
  apply two_value_one <;> omega

theorem two_value_from_differences (A B C D N dx dy dz : ℤ)
    (hN : N ≠ 0) (hdx : dx ≠ 0) (hdy : dy ≠ 0)
    (hAodd : ¬ (2 : ℤ) ∣ A) (hBodd : ¬ (2 : ℤ) ∣ B)
    (hCodd : ¬ (2 : ℤ) ∣ C) (hDodd : ¬ (2 : ℤ) ∣ D)
    (hdxeven : (2 : ℤ) ∣ dx) (hdyeven : (2 : ℤ) ∣ dy)
    (hdzeven : (2 : ℤ) ∣ dz)
    (hflag : A ^ 2 + D ^ 2 = B ^ 2 + C ^ 2)
    (hB : B ^ 2 - A ^ 2 = N * dx)
    (hC : C ^ 2 - A ^ 2 = N * dy)
    (hD : D ^ 2 - A ^ 2 = N * dz) :
    ∃ b c d : ℤ,
      (b = B ∨ b = -B) ∧ (c = C ∨ c = -C) ∧ (d = D ∨ d = -D) ∧
      (2 : ℤ) ^ padicValInt 2 N ∣ b - A ∧
      (2 : ℤ) ^ padicValInt 2 N ∣ c - A ∧
      (2 : ℤ) ^ padicValInt 2 N ∣ d - A ∧
      A - b - c + d ≠ 0 ∧
      padicValInt 2 (A - b - c + d) + 2 =
        2 * padicValInt 2 N + padicValInt 2 dx + padicValInt 2 dy := by
  have hpow := padicValInt_dvd (p := 2) N
  have hdivB : (2 : ℤ) ^ (padicValInt 2 N + 1) ∣ B ^ 2 - A ^ 2 := by
    rw [hB, pow_succ]
    exact mul_dvd_mul hpow hdxeven
  have hdivC : (2 : ℤ) ^ (padicValInt 2 N + 1) ∣ C ^ 2 - A ^ 2 := by
    rw [hC, pow_succ]
    exact mul_dvd_mul hpow hdyeven
  have hdivD : (2 : ℤ) ^ (padicValInt 2 N + 1) ∣ D ^ 2 - A ^ 2 := by
    rw [hD, pow_succ]
    exact mul_dvd_mul hpow hdzeven
  obtain ⟨b, hbsg, hb4, hb, hbplus⟩ := two_sign_choice A B hAodd hBodd hdivB
  obtain ⟨c, hcsg, hc4, hc, hcplus⟩ := two_sign_choice A C hAodd hCodd hdivC
  obtain ⟨d, hdsg, hd4, hd, _⟩ := two_sign_choice A D hAodd hDodd hdivD
  have hbsq := signed_sq hbsg
  have hcsq := signed_sq hcsg
  have hdsq := signed_sq hdsg
  have hbprod : (b - A) * (b + A) = N * dx := by
    linear_combination hbsq + hB
  have hcprod : (c - A) * (c + A) = N * dy := by
    linear_combination hcsq + hC
  have hbmn : b - A ≠ 0 := by
    intro h
    have := hbprod
    simp only [h, zero_mul] at this
    exact mul_ne_zero hN hdx this.symm
  have hcmn : c - A ≠ 0 := by
    intro h
    have := hcprod
    simp only [h, zero_mul] at this
    exact mul_ne_zero hN hdy this.symm
  have hbpn : b + A ≠ 0 := by
    intro h
    simp [h] at hbplus
  have hcpn : c + A ≠ 0 := by
    intro h
    simp [h] at hcplus
  have hFval := selected_F_two_value hAodd hb4 hc4 hd4
  have hFn : b + c + d - A ≠ 0 := by
    intro h
    simp [h] at hFval
  have hlf := lf_identity A b c d (by
    linear_combination hflag + hdsq - hbsq - hcsq)
  have hneg2 : (-2 : ℤ) ≠ 0 := by norm_num
  have hLn : A - b - c + d ≠ 0 := by
    intro h
    rw [h, zero_mul] at hlf
    exact mul_ne_zero (mul_ne_zero hneg2 hbmn) hcmn hlf.symm
  have hvb := congrArg (padicValInt 2) hbprod
  rw [padicValInt.mul hbmn hbpn, padicValInt.mul hN hdx, hbplus] at hvb
  have hvc := congrArg (padicValInt 2) hcprod
  rw [padicValInt.mul hcmn hcpn, padicValInt.mul hN hdy, hcplus] at hvc
  have hn2val : padicValInt 2 (-2) = 1 := by
    norm_num [padicValInt]
  have hvl := congrArg (padicValInt 2) hlf
  rw [padicValInt.mul hLn hFn,
    padicValInt.mul (mul_ne_zero hneg2 hbmn) hcmn,
    padicValInt.mul hneg2 hbmn, hFval, hn2val] at hvl
  refine ⟨b, c, d, hbsg, hcsg, hdsg, hb, hc, hd, hLn, ?_⟩
  omega

end BoundsValuation


end FourCorner
#print axioms FourCorner.BoundsValuation.odd_value_from_differences
#print axioms FourCorner.BoundsValuation.two_value_from_differences
