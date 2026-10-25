import FourCorner.CornerContent
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination

namespace FourCorner

private lemma two_square_from_double {p : ℕ} [Fact p.Prime]
    {a b : ZMod p} (hb : b ≠ 0) (hs : a ^ 2 = 2 * b ^ 2) :
    IsSquare (2 : ZMod p) := by
  refine ⟨a / b, ?_⟩
  rw [← pow_two, div_pow, eq_div_iff (pow_ne_zero 2 hb)]
  exact hs.symm

private lemma square_two_of_diagonal_sum {p : ℕ} [Fact p.Prime]
    {L X Y a₁ a₂ : ZMod p} (hL : L ≠ 0) (hXY : X + Y = L)
    (h₁ : a₁ ^ 2 = (L - X) ^ 2 + Y ^ 2)
    (h₂ : a₂ ^ 2 = X ^ 2 + (L - Y) ^ 2) :
    IsSquare (2 : ZMod p) := by
  by_cases hy : Y = 0
  · have hxl : X = L := by simpa [hy] using hXY
    have hx : X ≠ 0 := by rwa [hxl]
    apply two_square_from_double hx (a := a₂)
    simpa [hy, ← hxl, two_mul] using h₂
  · apply two_square_from_double hy (a := a₁)
    have hly : L - X = Y := by rw [← hXY]; ring
    simpa [hly, two_mul] using h₁

private lemma square_two_of_diagonal_difference {p : ℕ} [Fact p.Prime]
    {L X Y a₀ a₃ : ZMod p} (hL : L ≠ 0) (hXY : X = Y)
    (h₀ : a₀ ^ 2 = X ^ 2 + Y ^ 2)
    (h₃ : a₃ ^ 2 = (L - X) ^ 2 + (L - Y) ^ 2) :
    IsSquare (2 : ZMod p) := by
  by_cases hx : X = 0
  · have hy : Y = 0 := hXY.symm.trans hx
    apply two_square_from_double hL (a := a₃)
    simpa [hx, hy, two_mul] using h₃
  · apply two_square_from_double hx (a := a₀)
    simpa [← hXY, two_mul] using h₀

namespace IntegralModel

/-- At an odd prime not dividing the side, a vanishing sum of the radii
at opposite corners forces `2` to be a square in the residue field.
The conclusion uses the four original squared-distance equations. -/
theorem opposite_radius_sum_isSquare_two (M : IntegralModel)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hside : ¬ (p : ℤ) ∣ M.L)
    {c c' : Bool × Bool} (he : c.1 ≠ c'.1) (hh : c.2 ≠ c'.2)
    (hsum : ((M.cornerRadius c + M.cornerRadius c' : ℤ) : ZMod p) = 0) :
    IsSquare (2 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hL : (M.L : ZMod p) ≠ 0 := by
    intro h
    exact hside ((ZMod.intCast_zmod_eq_zero_iff_dvd M.L p).mp h)
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hodd
  have h₀ : (M.A₀ : ZMod p) ^ 2 = (M.X : ZMod p) ^ 2 + (M.Y : ZMod p) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) M.sq₀
  have h₁ : (M.A₁ : ZMod p) ^ 2 = ((M.L : ZMod p) - M.X) ^ 2 + (M.Y : ZMod p) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) M.sq₁
  have h₂ : (M.A₂ : ZMod p) ^ 2 = (M.X : ZMod p) ^ 2 + ((M.L : ZMod p) - M.Y) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) M.sq₂
  have h₃ : (M.A₃ : ZMod p) ^ 2 = ((M.L : ZMod p) - M.X) ^ 2 + ((M.L : ZMod p) - M.Y) ^ 2 := by
    simpa only [Int.cast_pow, Int.cast_add, Int.cast_sub] using
      congrArg (fun a : ℤ => (a : ZMod p)) M.sq₃
  have h03 (ha : (M.A₀ : ZMod p) + M.A₃ = 0) : IsSquare (2 : ZMod p) := by
    have hd : (2 : ZMod p) * M.L * ((M.X : ZMod p) + M.Y - M.L) = 0 := by
      linear_combination h₃ - h₀ + ((M.A₀ : ZMod p) - M.A₃) * ha
    have hdiag : (M.X : ZMod p) + M.Y = M.L :=
      sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (mul_ne_zero htwo hL))
    exact square_two_of_diagonal_sum hL hdiag h₁ h₂
  have h12 (ha : (M.A₁ : ZMod p) + M.A₂ = 0) : IsSquare (2 : ZMod p) := by
    have hd : (2 : ZMod p) * M.L * ((M.X : ZMod p) - M.Y) = 0 := by
      linear_combination h₁ - h₂ - ((M.A₁ : ZMod p) - M.A₂) * ha
    have hdiag : (M.X : ZMod p) = M.Y :=
      sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left (mul_ne_zero htwo hL))
    exact square_two_of_diagonal_difference hL hdiag h₀ h₃
  rcases c with ⟨e, h⟩
  rcases c' with ⟨e', h'⟩
  cases e <;> cases h <;> cases e' <;> cases h' <;>
    simp only [ne_eq, not_true_eq_false] at he hh
  all_goals simp only [cornerRadius, Int.cast_add] at hsum
  · exact h03 hsum
  · exact h12 (by simpa only [add_comm] using hsum)
  · exact h12 hsum
  · exact h03 (by simpa only [add_comm] using hsum)

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.opposite_radius_sum_isSquare_two
