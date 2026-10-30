import FourCorner.HasseNorms

/-! Literal square-condition interface and a reusable quadratic field norm criterion. -/
namespace FourCorner.HasseNormsInterface

open HasseNormWitness

/-- The four simultaneous nonzero squares in the manuscript, without chosen roots. -/
def LocalSquares (K : Type*) [Field K] (p : K) : Prop :=
  ∃ r : K, r ≠ 0 ∧ r ≠ 1 ∧ r ≠ -1 ∧
    (IsSquare (p * r) ∧ p * r ≠ 0) ∧
    (IsSquare (2 * (p - 1) * (r - 1)) ∧ 2 * (p - 1) * (r - 1) ≠ 0) ∧
    (IsSquare (2 * (p + 1) * (r + 1)) ∧ 2 * (p + 1) * (r + 1) ≠ 0) ∧
    (IsSquare ((p - 1) * r + p + 1) ∧ (p - 1) * r + p + 1 ≠ 0)

private theorem nonzero_square_root {K : Type*} [Field K] (c : K)
    (hc : IsSquare c) (h0 : c ≠ 0) : ∃ x : K, x ≠ 0 ∧ x ^ 2 = c := by
  obtain ⟨x, hx⟩ := hc
  refine ⟨x, ?_, ?_⟩
  · intro hz
    apply h0
    simpa [hz] using hx
  · simpa only [pow_two] using hx.symm

/-- Choosing ordered roots changes no local existence condition. -/
theorem localPoint_iff_localSquares {K : Type*} [Field K] (p : K) :
    Nonempty (HasseNorms.LocalPoint K p) ↔ LocalSquares K p := by
  constructor
  · rintro ⟨s⟩
    refine ⟨s.rho, s.rho_ne_zero, s.rho_ne_one, s.rho_ne_neg_one, ?_, ?_, ?_, ?_⟩
    · rw [← s.sqU]
      exact ⟨IsSquare.sq _, pow_ne_zero _ s.u_ne_zero⟩
    · rw [← s.sqV]
      exact ⟨IsSquare.sq _, pow_ne_zero _ s.v_ne_zero⟩
    · rw [← s.sqW]
      exact ⟨IsSquare.sq _, pow_ne_zero _ s.w_ne_zero⟩
    · rw [← s.sqT]
      exact ⟨IsSquare.sq _, pow_ne_zero _ s.t_ne_zero⟩
  · rintro ⟨r, hr0, hr1, hrm, hU, hV, hW, hT⟩
    obtain ⟨u, hu0, hu⟩ := nonzero_square_root _ hU.1 hU.2
    obtain ⟨v, hv0, hv⟩ := nonzero_square_root _ hV.1 hV.2
    obtain ⟨w, hw0, hw⟩ := nonzero_square_root _ hW.1 hW.2
    obtain ⟨t, ht0, ht⟩ := nonzero_square_root _ hT.1 hT.2
    exact ⟨⟨r, u, v, w, t, hr0, hr1, hrm, hu0, hv0, hw0, ht0, hu, hv, hw, ht⟩⟩

/-- Exact completion-by-completion form of the paper's Loc predicate. -/
theorem loc_iff_literal_conditions (p : ℚ) :
    HasseNorms.Loc p ↔ LocalSquares ℝ (p : ℝ) ∧
      ∀ (q : ℕ) [Fact q.Prime], LocalSquares ℚ_[q] (p : ℚ_[q]) := by
  simp only [HasseNorms.Loc, localPoint_iff_localSquares]

/-- Genuine field norm criterion for every rational scalar, including zero and
negative scalars. No reciprocity or local-global axiom is assumed. -/
theorem field_norm_iff_even_inert (r : ℚ) :
    (∃ x : SqrtTwo ℚ, Algebra.norm ℚ x = r) ↔
      ∀ (q : ℕ), q.Prime → q ≠ 2 → ¬ IsSquare (2 : ZMod q) →
        Even (padicValRat q r) := by
  constructor
  · rintro ⟨x, hx⟩ q hq hq2 hns
    letI : Fact q.Prime := ⟨hq⟩
    have hxn : x.norm = r := (SqrtTwoFieldNorm.algebra_norm_eq x).symm.trans hx
    obtain ⟨y, hy⟩ := HasseNorms.norm_at_completion r ⟨x, hxn⟩ q
    have he := HasseInertNorm.algebra_norm_val_even hq2
      (SqrtTwoGlobalNorm.nonsquare_two_completion hns) y
    rw [hy, Padic.valuation_ratCast] at he
    exact he
  · intro he
    by_cases hz : r = 0
    · subst r
      exact ⟨0, by simp⟩
    by_cases hp : 0 < r
    · exact SqrtTwoFieldNorm.exists_field_norm r
        (SqrtTwoGlobalNorm.positive_rat_norm_of_even_inert r hp he)
    have hn : 0 < -r := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hz)
    have hneg := SqrtTwoGlobalNorm.positive_rat_norm_of_even_inert (-r) hn
      (fun q hq hq2 hns => by simpa only [padicValRat.neg] using he q hq hq2 hns)
    apply SqrtTwoFieldNorm.exists_field_norm
    simpa only [neg_neg] using HasseNormWitness.exists_norm_neg hneg

#print axioms localPoint_iff_localSquares
#print axioms loc_iff_literal_conditions
#print axioms field_norm_iff_even_inert

end FourCorner.HasseNormsInterface
