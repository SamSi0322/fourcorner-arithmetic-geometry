import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

namespace FourCorner

/-- Divisibility of nonzero integers implies monotonicity of their finite valuations. -/
theorem pair_val_le_of_dvd {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hb : b ≠ 0) (hab : a ∣ b) :
    padicValNat p a.natAbs ≤ padicValNat p b.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  exact ((padicValInt_dvd_iff (padicValInt p a) b).mp
    (dvd_trans (padicValInt_dvd a) hab)).resolve_left hb

/-- For a nonzero sum, its valuation is at least the smaller summand valuation. -/
theorem pair_min_val_le_add {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hab : a + b ≠ 0) :
    min (padicValNat p a.natAbs) (padicValNat p b.natAbs) ≤
      padicValNat p (a + b).natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  let n := min (padicValInt p a) (padicValInt p b)
  have ha : (p : ℤ) ^ n ∣ a :=
    (padicValInt_dvd_iff n a).mpr (Or.inr (min_le_left _ _))
  have hb : (p : ℤ) ^ n ∣ b :=
    (padicValInt_dvd_iff n b).mpr (Or.inr (min_le_right _ _))
  exact ((padicValInt_dvd_iff n (a + b)).mp (dvd_add ha hb)).resolve_left hab

/-- For a nonzero difference, its valuation is at least the smaller input valuation. -/
theorem pair_min_val_le_sub {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hab : a - b ≠ 0) :
    min (padicValNat p a.natAbs) (padicValNat p b.natAbs) ≤
      padicValNat p (a - b).natAbs := by
  simpa only [Int.natAbs_neg, sub_eq_add_neg] using
    pair_min_val_le_add hp (a := a) (b := -b) (by simpa [sub_eq_add_neg] using hab)

/-- At an odd prime, multiplication by two preserves a nonzero integer's valuation. -/
theorem pair_val_two_mul {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {a : ℤ} (ha : a ≠ 0) :
    padicValNat p (2 * a).natAbs = padicValNat p a.natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : ¬p ∣ 2 := by
    intro h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rw [Int.natAbs_mul, padicValNat.mul (by decide) (Int.natAbs_ne_zero.mpr ha)]
  change padicValNat p 2 + padicValNat p a.natAbs = _
  rw [padicValNat.eq_zero_of_not_dvd hp2, zero_add]

/-- Odd-prime sum and difference have the same minimum valuation as the two inputs. -/
theorem pair_min_val_add_sub {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hadd : a + b ≠ 0) (hsub : a - b ≠ 0) :
    min (padicValNat p (a + b).natAbs) (padicValNat p (a - b).natAbs) =
      min (padicValNat p a.natAbs) (padicValNat p b.natAbs) := by
  apply le_antisymm
  · apply le_min
    · have h := pair_min_val_le_add hp (a := a + b) (b := a - b)
        (show a + b + (a - b) ≠ 0 by
          have he : a + b + (a - b) = 2 * a := by ring
          rw [he]; exact mul_ne_zero (by decide) ha)
      have he : a + b + (a - b) = 2 * a := by ring
      rw [he, pair_val_two_mul hp hodd ha] at h
      exact h
    · have h := pair_min_val_le_sub hp (a := a + b) (b := a - b)
        (show a + b - (a - b) ≠ 0 by
          have he : a + b - (a - b) = 2 * b := by ring
          rw [he]; exact mul_ne_zero (by decide) hb)
      have he : a + b - (a - b) = 2 * b := by ring
      rw [he, pair_val_two_mul hp hodd hb] at h
      exact h
  · exact le_min (pair_min_val_le_add hp hadd) (pair_min_val_le_sub hp hsub)

/-- Valuation factors the difference of squares into the two pair numerators. -/
theorem pair_val_add_sub_sum {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (hadd : a + b ≠ 0) (hsub : a - b ≠ 0) :
    padicValNat p (a + b).natAbs + padicValNat p (a - b).natAbs =
      padicValNat p (a ^ 2 - b ^ 2).natAbs := by
  let : Fact p.Prime := ⟨hp⟩
  have he : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by ring
  rw [he, Int.natAbs_mul,
    padicValNat.mul (Int.natAbs_ne_zero.mpr hadd) (Int.natAbs_ne_zero.mpr hsub)]

theorem pair_nat_clip_min_sum {x y e s : ℕ}
    (hmin : min x y = s) (hsum : x + y = e) :
    min (e - x) (e - y) = s ∧ (e - x) + (e - y) = e := by
  omega

theorem pair_nat_clip_pair_of_min_sum {x y e s : ℕ}
    (hmin : min x y = s) (hsum : x + y = e) :
    (e - x = s ∧ e - y = e - s) ∨
      (e - y = s ∧ e - x = e - s) := by
  omega

theorem pair_nat_clip_pair_of_min_zero_le_sum {x y e : ℕ}
    (hmin : min x y = 0) (hsum : e ≤ x + y) :
    (e - x = 0 ∧ e - y = e) ∨
      (e - y = 0 ∧ e - x = e) := by
  omega


/-- An exact difference valuation and input minimum determine the two denominator exponents. -/
theorem pair_denominator_pattern_of_exact_difference {p s e : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) {a b : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hadd : a + b ≠ 0) (hsub : a - b ≠ 0)
    (hmin : min (padicValNat p a.natAbs) (padicValNat p b.natAbs) = s)
    (hdiff : padicValNat p (a ^ 2 - b ^ 2).natAbs = e) :
    (e - padicValNat p (a + b).natAbs = s ∧
      e - padicValNat p (a - b).natAbs = e - s) ∨
    (e - padicValNat p (a - b).natAbs = s ∧
      e - padicValNat p (a + b).natAbs = e - s) := by
  exact pair_nat_clip_pair_of_min_sum
    ((pair_min_val_add_sub hp hodd ha hb hadd hsub).trans hmin)
    ((pair_val_add_sub_sum hp hadd hsub).trans hdiff)

/-- When an input is a prime unit, divisibility of the squared difference gives all-or-none
cancellation of the denominator's prime power between the sum and difference. -/
theorem pair_denominator_pattern_of_unit {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) {a b L : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hadd : a + b ≠ 0) (hsub : a - b ≠ 0)
    (hunit : ¬(p : ℤ) ∣ a) (hdiv : L ∣ a ^ 2 - b ^ 2) :
    (padicValNat p L.natAbs - padicValNat p (a + b).natAbs = 0 ∧
      padicValNat p L.natAbs - padicValNat p (a - b).natAbs = padicValNat p L.natAbs) ∨
    (padicValNat p L.natAbs - padicValNat p (a - b).natAbs = 0 ∧
      padicValNat p L.natAbs - padicValNat p (a + b).natAbs = padicValNat p L.natAbs) := by
  apply pair_nat_clip_pair_of_min_zero_le_sum
  · rw [pair_min_val_add_sub hp hodd ha hb hadd hsub]
    have hu : padicValNat p a.natAbs = 0 := padicValInt.eq_zero_of_not_dvd hunit
    simp [hu]
  · rw [pair_val_add_sub_sum hp hadd hsub]
    apply pair_val_le_of_dvd hp _ hdiv
    have he : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by ring
    rw [he]
    exact mul_ne_zero hadd hsub

end FourCorner
