import HpInfiniteArithmetic
import HpDomainArithmetic

namespace FourCorner.HpFamilyDyadicValuation

open HpInfiniteArithmetic

def NN (j : ℕ) : ℕ := 3+154*j
def MM (j : ℕ) : ℕ := NN j+2
def DD (j : ℕ) : ℕ := (NN j)^2+2*(MM j)^2

theorem N_odd (j : ℕ) : Odd (NN j) := by rw [Nat.odd_iff];unfold NN;omega
theorem M_odd (j : ℕ) : Odd (MM j) := by
  have hn := N_odd j
  rw [Nat.odd_iff] at hn ⊢
  unfold MM
  omega
theorem D_odd (j : ℕ) : Odd (DD j) := by
  have hn : Odd ((NN j)^2) := (N_odd j).pow
  rw [Nat.odd_iff] at hn ⊢
  unfold DD
  omega

theorem N_cast (j : ℕ) : (NN j : ℚ)=N j := by simp [NN,N]
theorem M_cast (j : ℕ) : (MM j : ℚ)=M j := by simp [MM,M,N_cast]
theorem D_cast (j : ℕ) : (DD j : ℚ)=D j := by simp [DD,D,N_cast,M_cast]

theorem odd_nat_valuation_zero (n : ℕ) (hn : Odd n) : padicValRat 2 (n : ℚ)=0 := by
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd hn.not_two_dvd_nat]
  rfl

theorem r_valuation (j : ℕ) : padicValRat 2 (r j)=3 := by
  have hn0 : (NN j : ℚ) ≠ 0 := by
    rw [N_cast]
    have hh := N_ge j
    linarith
  have hm0 : (MM j : ℚ) ≠ 0 := by
    rw [M_cast]
    have hh := N_ge j
    dsimp [M]
    linarith
  have hd0 : (DD j : ℚ) ≠ 0 := by rw [D_cast];exact ne_of_gt (D_pos j)
  have he : r j=8*(MM j : ℚ)*(NN j : ℚ)/(DD j : ℚ) := by rw [N_cast,M_cast,D_cast];rfl
  have hv8 : padicValRat 2 (8 : ℚ)=3 := by
    rw [show (8 : ℚ)=(2 : ℚ)^3 by norm_num,padicValRat.pow,
      show padicValRat 2 (2 : ℚ)=1 from padicValRat.self (by norm_num : 1<2)]
    norm_num
  rw [he,padicValRat.div (mul_ne_zero (mul_ne_zero (by norm_num) hm0) hn0) hd0,
    padicValRat.mul (mul_ne_zero (by norm_num) hm0) hn0,padicValRat.mul (by norm_num) hm0,
    odd_nat_valuation_zero _ (N_odd j),odd_nat_valuation_zero _ (M_odd j),odd_nat_valuation_zero _ (D_odd j)]
  rw [hv8]
  norm_num

theorem b_valuation (j : ℕ) : padicValRat 2 (p j+1)=5 := by
  have hr0 := anchor_nonzero j
  have he : p j+1=(r j)^2/2 := by linear_combination (-1/2 : ℚ)*r_square j
  have hv2 : padicValRat 2 (2 : ℚ)=1 := by simpa using padicValRat.self (by norm_num : 1<2)
  rw [he,padicValRat.div (pow_ne_zero _ hr0) (by norm_num),padicValRat.pow,r_valuation,hv2]
  norm_num

#print axioms r_valuation
#print axioms b_valuation

end FourCorner.HpFamilyDyadicValuation
