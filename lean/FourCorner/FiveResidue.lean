import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace FourCorner

/-- Two nonzero squares modulo five can sum to a square only when that sum is zero. -/
lemma five_square_sum_units_zero (x y a : ZMod 5)
    (hx : x ≠ 0) (hy : y ≠ 0) (ha : a ^ 2 = x ^ 2 + y ^ 2) : a = 0 := by
  have h : ∀ x y a : ZMod 5, x ≠ 0 → y ≠ 0 → a ^ 2 = x ^ 2 + y ^ 2 → a = 0 := by
    decide
  exact h x y a hx hy ha

/-- Every square modulo five is zero, one, or four. -/
lemma five_square_values (a : ZMod 5) : a ^ 2 = 0 ∨ a ^ 2 = 1 ∨ a ^ 2 = 4 := by
  fin_cases a <;> decide

/-- Four squares modulo five cannot all be distinct. -/
lemma five_four_squares_not_injective (r : Fin 4 → ZMod 5) :
    ¬ Function.Injective (fun i => (r i) ^ 2) := by
  let f : Fin 4 → {a : ZMod 5 // a = 0 ∨ a = 1 ∨ a = 4} :=
    fun i => ⟨(r i) ^ 2, five_square_values (r i)⟩
  have hcard : Fintype.card {a : ZMod 5 // a = 0 ∨ a = 1 ∨ a = 4} <
      Fintype.card (Fin 4) := by decide
  intro h
  apply Fintype.not_injective_of_card_lt f hcard
  intro i j hij
  exact h (congrArg Subtype.val hij)

end FourCorner
