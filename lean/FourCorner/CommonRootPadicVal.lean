import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms

namespace FourCorner

variable {p : ℕ} [Fact p.Prime]

/-- Negation preserves the integer-valued p-adic valuation, including at zero. -/
theorem commonRoot_val_neg (x : ℚ_[p]) : (-x).valuation = x.valuation := by
  by_cases hx : x = 0
  · simp [hx]
  have h := (Padic.addValuation (p := p)).map_neg x
  rw [Padic.addValuation.apply (neg_ne_zero.mpr hx), Padic.addValuation.apply hx] at h
  exact WithTop.coe_inj.mp h

/-- Different finite valuations prevent cancellation of a sum. -/
theorem commonRoot_add_ne_zero_of_val_ne {x y : ℚ_[p]}
    (hval : x.valuation ≠ y.valuation) : x + y ≠ 0 := by
  intro h
  have he : x = -y := eq_neg_of_add_eq_zero_left h
  exact hval (he ▸ commonRoot_val_neg y)

/-- The valuation of a sum with unequal input valuations is their minimum. -/
theorem commonRoot_val_add_of_ne {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hval : x.valuation ≠ y.valuation) :
    (x + y).valuation = min x.valuation y.valuation := by
  have hne : Padic.addValuation x ≠ Padic.addValuation y := by
    rw [Padic.addValuation.apply hx, Padic.addValuation.apply hy]
    exact fun h => hval (WithTop.coe_inj.mp h)
  have h := (Padic.addValuation (p := p)).map_add_of_distinct_val hne
  rw [Padic.addValuation.apply (commonRoot_add_ne_zero_of_val_ne hval),
    Padic.addValuation.apply hx, Padic.addValuation.apply hy] at h
  norm_cast at h

/-- The valuation of a difference with unequal input valuations is their minimum. -/
theorem commonRoot_val_sub_of_ne {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0)
    (hval : x.valuation ≠ y.valuation) :
    (x - y).valuation = min x.valuation y.valuation := by
  simpa only [sub_eq_add_neg, commonRoot_val_neg] using
    commonRoot_val_add_of_ne hx (neg_ne_zero.mpr hy)
      (by simpa only [commonRoot_val_neg] using hval)

theorem commonRoot_even_val_of_isSquare {x : ℚ_[p]} (hx : IsSquare x) :
    Even x.valuation := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y.valuation, ?_⟩
  simpa only [pow_two, Nat.cast_ofNat, two_mul] using Padic.valuation_pow y 2

theorem commonRoot_norm_lt_one_iff {x : ℚ_[p]} (hx : x ≠ 0) :
    ‖x‖ < 1 ↔ 0 < x.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation hx, ← zpow_zero (p : ℝ),
    zpow_lt_zpow_iff_right₀, neg_lt_zero]
  exact_mod_cast (Fact.out : p.Prime).one_lt

theorem commonRoot_val_two (hp : p ≠ 2) : (2 : ℚ_[p]).valuation = 0 := by
  rw [Padic.valuation_ofNat, padicValNat.eq_zero_of_not_dvd, Nat.cast_zero]
  exact fun h => hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)

theorem commonRoot_val_div {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / y).valuation = x.valuation - y.valuation := by
  rw [div_eq_mul_inv, Padic.valuation_mul hx (inv_ne_zero hy), Padic.valuation_inv,
    sub_eq_add_neg]



/-- Different finite valuations prevent cancellation of a difference. -/
theorem commonRoot_sub_ne_zero_of_val_ne {x y : ℚ_[p]}
    (hval : x.valuation ≠ y.valuation) : x - y ≠ 0 := by
  intro h
  exact hval (congrArg Padic.valuation (sub_eq_zero.mp h))

/-- A perturbation of one by an element of positive valuation is a unit. -/
theorem commonRoot_val_eq_zero_of_sub_one_pos {x : ℚ_[p]}
    (hpos : 0 < (x - 1).valuation) : x.valuation = 0 := by
  have hn : x - 1 ≠ 0 := by
    intro h
    simp [h] at hpos
  have h := commonRoot_val_add_of_ne hn (one_ne_zero : (1 : ℚ_[p]) ≠ 0)
    (show (x - 1).valuation ≠ (1 : ℚ_[p]).valuation by
      rw [Padic.valuation_one]
      exact ne_of_gt hpos)
  simpa only [sub_add_cancel, Padic.valuation_one, min_eq_right (le_of_lt hpos)] using h

/-- At an odd prime, a point near one has its sum with one of valuation zero. -/
theorem commonRoot_val_add_one_of_sub_one_pos (hodd : p ≠ 2) {x : ℚ_[p]}
    (hpos : 0 < (x - 1).valuation) : (x + 1).valuation = 0 := by
  have hn : x - 1 ≠ 0 := by
    intro h
    simp [h] at hpos
  have htwo : (2 : ℚ_[p]) ≠ 0 := by exact_mod_cast (show (2 : ℚ) ≠ 0 by decide)
  have h := commonRoot_val_add_of_ne hn htwo
    (show (x - 1).valuation ≠ (2 : ℚ_[p]).valuation by
      rw [commonRoot_val_two hodd]
      exact ne_of_gt hpos)
  have he : x - 1 + 2 = x + 1 := by ring
  simpa only [he, commonRoot_val_two hodd, min_eq_right (le_of_lt hpos)] using h

end FourCorner
