import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FourCorner

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The square-residue table modulo seventeen. The outer test leaves only
`i = 4` and `i = 13`; the inner table checks the two parameters `c` and `b`.
This finite computation is reduced and checked by the Lean kernel. -/
private lemma seventeen_residue_table :
    ∀ i : ZMod 17, i ^ 2 = -1 →
    ∀ c b : ZMod 17, b ≠ 0 →
    IsSquare c → IsSquare (c + b) → IsSquare (c + i * b) →
    IsSquare (c + (1 + i) * b) →
    c ≠ 0 ∧ c + b ≠ 0 ∧ c + i * b ≠ 0 ∧
      c + (1 + i) * b ≠ 0 ∧ 2 * c + (1 + i) * b = 0 := by
  decide

/-- The possible normalized product sums are nonsquares, as are their doubles. -/
private lemma seventeen_product_table :
    ∀ x y : ZMod 17, x ^ 2 = -1 → y ^ 2 = 1 →
      ¬ IsSquare (x + y) ∧ ¬ IsSquare (2 * (x + y)) := by
  decide

/-- The critical seventeen square pattern, including both product-sum
obstructions and the two opposite-corner cancellations. -/
theorem seventeen_square_pattern (a₀ a₁ a₂ a₃ i b : ZMod 17)
    (hi : i ^ 2 = -1) (hb : b ≠ 0)
    (h₁ : a₁ ^ 2 = a₀ ^ 2 + b)
    (h₂ : a₂ ^ 2 = a₀ ^ 2 + i * b)
    (h₃ : a₃ ^ 2 = a₀ ^ 2 + (1 + i) * b) :
    a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0 ∧
    ¬ IsSquare (a₀ * a₃ + a₁ * a₂) ∧
    ¬ IsSquare (2 * (a₀ * a₃ + a₁ * a₂)) ∧
    a₀ ^ 2 + a₃ ^ 2 = 0 ∧ a₁ ^ 2 + a₂ ^ 2 = 0 ∧
    2 * a₀ ^ 2 + (1 + i) * b = 0 := by
  have hs₀ : IsSquare (a₀ ^ 2) := ⟨a₀, by ring⟩
  have hs₁ : IsSquare (a₀ ^ 2 + b) := ⟨a₁, by rw [← h₁]; ring⟩
  have hs₂ : IsSquare (a₀ ^ 2 + i * b) := ⟨a₂, by rw [← h₂]; ring⟩
  have hs₃ : IsSquare (a₀ ^ 2 + (1 + i) * b) := ⟨a₃, by rw [← h₃]; ring⟩
  obtain ⟨hc₀, hc₁, hc₂, hc₃, he⟩ :=
    seventeen_residue_table i hi (a₀ ^ 2) b hb hs₀ hs₁ hs₂ hs₃
  have ha₀ : a₀ ≠ 0 := fun hz => hc₀ (by rw [hz]; norm_num)
  have ha₁ : a₁ ≠ 0 := fun hz => hc₁ (by rw [← h₁, hz]; norm_num)
  have ha₂ : a₂ ≠ 0 := fun hz => hc₂ (by rw [← h₂, hz]; norm_num)
  have ha₃ : a₃ ≠ 0 := fun hz => hc₃ (by rw [← h₃, hz]; norm_num)
  have h03 : a₀ ^ 2 + a₃ ^ 2 = 0 := by linear_combination h₃ + he
  have h12 : a₁ ^ 2 + a₂ ^ 2 = 0 := by linear_combination h₁ + h₂ + he
  have hbc : b = (i - 1) * a₀ ^ 2 := by
    have hi1 : i + 1 ≠ 0 := by
      intro hz
      have hz' : i = -1 := by linear_combination hz
      rw [hz'] at hi
      exact (by decide : (1 : ZMod 17) ≠ -1) hi
    apply (mul_left_cancel₀ hi1)
    linear_combination he - a₀ ^ 2 * hi
  have h₁' : a₁ ^ 2 = i * a₀ ^ 2 := by rw [h₁, hbc]; ring
  have h₂' : a₂ ^ 2 = -i * a₀ ^ 2 := by
    linear_combination h12 - h₁'
  have hp : (a₀ * a₃ / a₀ ^ 2) ^ 2 = -1 := by
    field_simp
    linear_combination h03
  have hq : (a₁ * a₂ / a₀ ^ 2) ^ 2 = 1 := by
    field_simp
    linear_combination a₂ ^ 2 * h₁' + i * a₀ ^ 2 * h₂' - a₀ ^ 4 * hi
  obtain ⟨hn, hn2⟩ := seventeen_product_table _ _ hp hq
  have hn' : ¬ IsSquare (a₀ * a₃ + a₁ * a₂) := by
    intro hs
    apply hn
    simpa only [add_div] using hs.div hs₀
  have hn2' : ¬ IsSquare (2 * (a₀ * a₃ + a₁ * a₂)) := by
    intro hs
    apply hn2
    rw [← add_div, ← mul_div_assoc]
    exact hs.div hs₀
  exact ⟨ha₀, ha₁, ha₂, ha₃, hn', hn2', h03, h12, he⟩

private lemma seventeen_ratio_of_sq (a c r : ZMod 17) (hc : c ≠ 0)
    (hs : a ^ 2 = r ^ 2 * c ^ 2) : a / c = r ∨ a / c = -r := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [div_pow, hs, mul_div_cancel_right₀ _ (pow_ne_zero 2 hc)]

/-- The two normalized critical-seventeen patterns. For `i = 4` the first
three nontrivial radius ratios are `±2`, `±8`, `±4`; for `i = -4` the
first two ratios are interchanged. -/
theorem seventeen_square_pattern_ratios (a₀ a₁ a₂ a₃ i b : ZMod 17)
    (hi : i ^ 2 = -1) (hb : b ≠ 0)
    (h₁ : a₁ ^ 2 = a₀ ^ 2 + b)
    (h₂ : a₂ ^ 2 = a₀ ^ 2 + i * b)
    (h₃ : a₃ ^ 2 = a₀ ^ 2 + (1 + i) * b) :
    a₀ ≠ 0 ∧
    ((i = 4 ∧ (a₁ / a₀ = 2 ∨ a₁ / a₀ = -2) ∧
      (a₂ / a₀ = 8 ∨ a₂ / a₀ = -8) ∧ (a₃ / a₀ = 4 ∨ a₃ / a₀ = -4)) ∨
     (i = -4 ∧ (a₁ / a₀ = 8 ∨ a₁ / a₀ = -8) ∧
      (a₂ / a₀ = 2 ∨ a₂ / a₀ = -2) ∧ (a₃ / a₀ = 4 ∨ a₃ / a₀ = -4))) := by
  obtain ⟨ha₀, _, _, _, _, _, h03, h12, he⟩ :=
    seventeen_square_pattern a₀ a₁ a₂ a₃ i b hi hb h₁ h₂ h₃
  have hi_cases : i = 4 ∨ i = -4 := by
    have ht : ∀ j : ZMod 17, j ^ 2 = -1 → j = 4 ∨ j = -4 := by decide
    exact ht i hi
  have h17 : (17 : ZMod 17) = 0 := by decide
  have h34 : (34 : ZMod 17) = 0 := by decide
  have h51 : (51 : ZMod 17) = 0 := by decide
  have h85 : (85 : ZMod 17) = 0 := by decide
  refine ⟨ha₀, ?_⟩
  rcases hi_cases with hi4 | hi4
  · left
    refine ⟨hi4, ?_, ?_, ?_⟩
    all_goals apply seventeen_ratio_of_sq _ _ _ ha₀
    · rw [hi4] at he
      linear_combination (norm := ring_nf) h₁ + (7 : ZMod 17) * he
      simp [h17, h34]
    · rw [hi4] at h₂ he
      linear_combination (norm := ring_nf) h₂ + (11 : ZMod 17) * he
      simp [h85, h51]
    · linear_combination (norm := ring_nf) h03
      simp [h17]
  · right
    refine ⟨hi4, ?_, ?_, ?_⟩
    all_goals apply seventeen_ratio_of_sq _ _ _ ha₀
    · rw [hi4] at he
      linear_combination (norm := ring_nf) h₁ + (11 : ZMod 17) * he
      simp [h85, h34]
    · rw [hi4] at h₂ he
      linear_combination (norm := ring_nf) h₂ + (7 : ZMod 17) * he
      simp [h17]
    · linear_combination (norm := ring_nf) h03
      simp [h17]

end FourCorner

#print axioms FourCorner.seventeen_square_pattern

#print axioms FourCorner.seventeen_square_pattern_ratios
