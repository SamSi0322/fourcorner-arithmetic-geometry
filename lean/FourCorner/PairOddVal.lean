import FourCorner.PairRatDen
import FourCorner.PairValArithmetic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace FourCorner

private theorem val_divisor_unit {p : ℕ} (hp : p.Prime) {G A : ℤ}
    (hG : G ≠ 0) (hA : A ≠ 0) (hd : G ∣ A) (hu : ¬ (p : ℤ) ∣ A / G) :
    padicValNat p A.natAbs = padicValNat p G.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have hq : A/G ≠ 0 := by
    intro hq
    have hh := Int.mul_ediv_cancel' hd
    rw [hq, mul_zero] at hh
    exact hA hh.symm
  have hqu : ¬ p ∣ (A/G).natAbs := by
    intro hh; exact hu (Int.natCast_dvd.mpr hh)
  rw [← Int.mul_ediv_cancel' hd, Int.natAbs_mul,
    padicValNat.mul (Int.natAbs_ne_zero.mpr hG) (Int.natAbs_ne_zero.mpr hq),
    padicValNat.eq_zero_of_not_dvd hqu, add_zero]

/-- Odd-prime denominator exponents from the exact content normalization.
This lemma has no bounded depth or relative-size assumption. -/
theorem odd_pair_den_values {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (A B L G H K : ℤ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hL : L ≠ 0) (hG : G ≠ 0) (hH : H ≠ 0)
    (hadd : A+B ≠ 0) (hsub : A-B ≠ 0)
    (hf : G^2 * H = L) (hgA : G ∣ A) (hgB : G ∣ B)
    (hunits : (p : ℤ) ∣ H → ¬ (p : ℤ) ∣ A/G ∧ ¬ (p : ℤ) ∣ B/G)
    (hdiff : A^2-B^2 = L*K)
    (hkg : (p : ℤ) ∣ G → ¬ (p : ℤ) ∣ K) :
    min (padicValNat p (((A+B : ℤ) : ℚ)/L).den)
      (padicValNat p (((A-B : ℤ) : ℚ)/L).den) = padicValNat p G.natAbs ∧
    padicValNat p (((A+B : ℤ) : ℚ)/L).den +
      padicValNat p (((A-B : ℤ) : ℚ)/L).den = padicValNat p L.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have hk : K ≠ 0 := by
    intro hk
    have he : A^2-B^2 ≠ 0 := by
      rw [show A^2-B^2 = (A+B)*(A-B) by ring]
      exact mul_ne_zero hadd hsub
    apply he
    rw [hdiff,hk,mul_zero]
  have he : padicValNat p L.natAbs =
      2 * padicValNat p G.natAbs + padicValNat p H.natAbs := by
    rw [← hf, Int.natAbs_mul, Int.natAbs_pow,
      padicValNat.mul (pow_ne_zero _ (Int.natAbs_ne_zero.mpr hG))
        (Int.natAbs_ne_zero.mpr hH), padicValNat.pow]
  have hs := pair_val_add_sub_sum hp hadd hsub
  rw [hdiff, Int.natAbs_mul,
    padicValNat.mul (Int.natAbs_ne_zero.mpr hL) (Int.natAbs_ne_zero.mpr hk)] at hs
  have hm := pair_min_val_add_sub hp hodd hA hB hadd hsub
  have hsG := pair_val_le_of_dvd hp hadd (dvd_add hgA hgB)
  have htG := pair_val_le_of_dvd hp hsub (dvd_sub hgA hgB)
  rw [padicValNat_rat_div_den_eq hp _ _ hadd hL,
    padicValNat_rat_div_den_eq hp _ _ hsub hL]
  by_cases hg : (p : ℤ) ∣ G
  · have hkzero : padicValNat p K.natAbs = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => hkg hg (Int.natCast_dvd.mpr h))
    rw [hkzero,add_zero] at hs
    by_cases hh : (p : ℤ) ∣ H
    · obtain ⟨huA,huB⟩ := hunits hh
      have hvA := val_divisor_unit hp hG hA hgA huA
      have hvB := val_divisor_unit hp hG hB hgB huB
      rw [hvA,hvB,min_self] at hm
      omega
    · have hz : padicValNat p H.natAbs = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun h => hh (Int.natCast_dvd.mpr h))
      rw [hz,add_zero] at he
      omega
  · have hgzero : padicValNat p G.natAbs = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => hg (Int.natCast_dvd.mpr h))
    by_cases hh : (p : ℤ) ∣ H
    · obtain ⟨huA,huB⟩ := hunits hh
      have hvA := val_divisor_unit hp hG hA hgA huA
      have hvB := val_divisor_unit hp hG hB hgB huB
      rw [hvA,hvB,hgzero,min_self] at hm
      omega
    · have hz : padicValNat p H.natAbs = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun h => hh (Int.natCast_dvd.mpr h))
      rw [hz,hgzero] at he
      omega

end FourCorner
#print axioms FourCorner.odd_pair_den_values
