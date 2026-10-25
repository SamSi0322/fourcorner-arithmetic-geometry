import FourCorner.CommonRootMatrixLocal
import FourCorner.CommonRootSource

namespace FourCorner

variable {p : ℕ} [Fact p.Prime]

/-- A parameter of negative valuation has discriminant of exactly twice
that valuation. This holds also at the prime two. -/
theorem commonRoot_discriminant_val_of_neg {t : ℚ_[p]} (ht : t.valuation < 0) :
    (t ^ 2 - 1).valuation = 2 * t.valuation := by
  have ht0 : t ≠ 0 := by
    intro hz
    simp [hz] at ht
  have hpow : (t ^ 2).valuation < 0 := by
    rw [Padic.valuation_pow]
    norm_num
    omega
  have hv := commonRoot_val_sub_of_ne (pow_ne_zero 2 ht0)
    (one_ne_zero : (1 : ℚ_[p]) ≠ 0)
    (by simpa only [Padic.valuation_one] using ne_of_lt hpow)
  rw [Padic.valuation_one, min_eq_left hpow.le] at hv
  simpa only [Padic.valuation_pow, Nat.cast_ofNat] using hv

/-- An odd discriminant valuation must be positive: negative parameter
valuation gives even depth, while nonnegative parameter valuation gives
nonnegative discriminant depth. -/
theorem commonRoot_discriminant_val_pos_of_odd {t : ℚ_[p]}
    (hodd : Odd (t ^ 2 - 1).valuation) : 0 < (t ^ 2 - 1).valuation := by
  have hd0 : t ^ 2 - 1 ≠ 0 := by
    intro hz
    simp [hz] at hodd
  have ht : 0 ≤ t.valuation := by
    by_contra hn
    have hv := commonRoot_discriminant_val_of_neg (lt_of_not_ge hn)
    rw [hv] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  have hle := Padic.le_valuation_add (x := t ^ 2) (y := -1)
    (by simpa only [sub_eq_add_neg] using hd0)
  rw [← sub_eq_add_neg, Padic.valuation_pow, commonRoot_val_neg,
    Padic.valuation_one] at hle
  have hmin : min ((2 : ℤ) * t.valuation) 0 = 0 := min_eq_right (by omega)
  norm_num only [Nat.cast_ofNat] at hle
  rw [hmin] at hle
  obtain ⟨k, hk⟩ := hodd
  omega

/-- A prime dividing a squarefree natural contributes odd valuation to
that natural times any nonzero rational square, in the actual p-adic field. -/
theorem squarefree_mul_rat_sq_padic_valuation_odd {Δ : ℕ} {q : ℚ} {d : ℚ_[p]}
    (hΔ : Squarefree Δ) (hpΔ : p ∣ Δ) (hq : q ≠ 0)
    (hd : d = (Δ : ℚ_[p]) * (q : ℚ_[p]) ^ 2) : Odd d.valuation := by
  have hΔp : (Δ : ℚ_[p]) ≠ 0 := by exact_mod_cast hΔ.ne_zero
  have hqp : (q : ℚ_[p]) ≠ 0 := by exact_mod_cast hq
  rw [hd, Padic.valuation_mul hΔp (pow_ne_zero 2 hqp), Padic.valuation_natCast,
    squarefree_padicValNat_eq_one hΔ hpΔ, Padic.valuation_pow, Padic.valuation_ratCast]
  refine ⟨padicValRat p q, ?_⟩
  norm_num
  omega

/-- Odd rational valuation forces the prime to divide the natural factor
of a natural times a rational square. Squarefreeness is not required. -/
theorem prime_dvd_nat_of_odd_rat_square_factor {Δ : ℕ} {q d : ℚ}
    (hq : q ≠ 0) (hd : d = (Δ : ℚ) * q ^ 2)
    (hodd : Odd (padicValRat p d)) : p ∣ Δ := by
  by_cases hΔ : Δ = 0
  · rw [hΔ]
    exact dvd_zero p
  by_contra hn
  have hΔq : (Δ : ℚ) ≠ 0 := by exact_mod_cast hΔ
  rw [hd, padicValRat.mul hΔq (pow_ne_zero 2 hq), padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd hn, padicValRat.pow] at hodd
  norm_num only [Nat.cast_zero, zero_add, Nat.cast_ofNat] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

namespace CommonRootSource

variable {t : ℚ_[p]}

/-- Every actual ordered source with odd discriminant depth has positive depth. -/
theorem discriminant_valuation_pos_of_odd (_S : CommonRootSource ℚ_[p] t)
    (hodd : Odd (t ^ 2 - 1).valuation) : 0 < (t ^ 2 - 1).valuation :=
  commonRoot_discriminant_val_pos_of_odd hodd

/-- A prime factor of the squarefree discriminant kernel has positive odd
valuation at the corresponding actual local source. -/
theorem discriminant_valuation_odd_pos_of_squarefree
    (S : CommonRootSource ℚ_[p] t) {Δ : ℕ} {q : ℚ}
    (hΔ : Squarefree Δ) (hpΔ : p ∣ Δ) (hq : q ≠ 0)
    (hd : t ^ 2 - 1 = (Δ : ℚ_[p]) * (q : ℚ_[p]) ^ 2) :
    Odd (t ^ 2 - 1).valuation ∧ 0 < (t ^ 2 - 1).valuation := by
  have hv := squarefree_mul_rat_sq_padic_valuation_odd hΔ hpΔ hq hd
  exact ⟨hv, S.discriminant_valuation_pos_of_odd hv⟩

end CommonRootSource
end FourCorner

#print axioms FourCorner.commonRoot_discriminant_val_of_neg
#print axioms FourCorner.commonRoot_discriminant_val_pos_of_odd
#print axioms FourCorner.squarefree_mul_rat_sq_padic_valuation_odd
#print axioms FourCorner.prime_dvd_nat_of_odd_rat_square_factor
#print axioms FourCorner.CommonRootSource.discriminant_valuation_odd_pos_of_squarefree
