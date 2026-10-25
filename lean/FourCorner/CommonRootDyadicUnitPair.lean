import FourCorner.CommonRootPadicVal

namespace FourCorner

private theorem dyadic_unit_toZMod_eq_one {x : ℤ_[2]} (hx : ‖x‖ = 1) :
    PadicInt.toZMod x = 1 := by
  have hn : PadicInt.toZMod x ≠ 0 := by
    intro h
    have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
      exact h
    have hn : ‖x‖ < 1 := by
      simpa only [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] using hm
    rw [hx] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact (hcases _).resolve_left hn

/-- The sum of two dyadic units has strictly positive valuation when nonzero. -/
theorem commonRoot_dyadic_unit_add_pos {x y : ℚ_[2]}
    (hx : x ≠ 0) (hy : y ≠ 0) (hvx : x.valuation = 0) (hvy : y.valuation = 0)
    (hs : x + y ≠ 0) : 0 < (x + y).valuation := by
  have hnx : ‖x‖ = 1 := by rw [Padic.norm_eq_zpow_neg_valuation hx, hvx]; simp
  have hny : ‖y‖ = 1 := by rw [Padic.norm_eq_zpow_neg_valuation hy, hvy]; simp
  let X : ℤ_[2] := ⟨x, hnx.le⟩
  let Y : ℤ_[2] := ⟨y, hny.le⟩
  have hX : PadicInt.toZMod X = 1 := dyadic_unit_toZMod_eq_one hnx
  have hY : PadicInt.toZMod Y = 1 := dyadic_unit_toZMod_eq_one hny
  have hm : X + Y ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_add, hX, hY]
    decide
  have hn : ‖X + Y‖ < 1 := by
    simpa only [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] using hm
  exact (commonRoot_norm_lt_one_iff hs).mp hn

/-- For two dyadic units with nonzero sum and difference, the smaller valuation is one. -/
theorem commonRoot_dyadic_unit_pair_min {x y : ℚ_[2]}
    (hx : x ≠ 0) (hy : y ≠ 0) (hvx : x.valuation = 0) (hvy : y.valuation = 0)
    (hs : x + y ≠ 0) (hd : x - y ≠ 0) :
    min (x + y).valuation (x - y).valuation = 1 := by
  have hsum := commonRoot_dyadic_unit_add_pos hx hy hvx hvy hs
  have hdiff : 0 < (x - y).valuation := by
    simpa only [sub_eq_add_neg] using commonRoot_dyadic_unit_add_pos hx
      (neg_ne_zero.mpr hy) hvx (by simpa only [commonRoot_val_neg] using hvy)
      (by simpa only [sub_eq_add_neg] using hd)
  have htwo : (2 : ℚ_[2]) ≠ 0 := by exact_mod_cast (show (2 : ℚ) ≠ 0 by decide)
  have heq : x + y + (x - y) = 2 * x := by ring
  have hle := Padic.le_valuation_add (show x + y + (x - y) ≠ 0 by
    rw [heq]; exact mul_ne_zero htwo hx)
  rw [heq, Padic.valuation_mul htwo hx, show (2 : ℚ_[2]).valuation = 1 from Padic.valuation_p,
    hvx, add_zero] at hle
  omega

end FourCorner
