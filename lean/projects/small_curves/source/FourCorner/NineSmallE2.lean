import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import FourCorner.NineFlexGroup

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FourCorner

/-- Fermat's fourth-power theorem over the rationals, obtained by clearing
the two fourth-power denominators and applying the integer descent theorem. -/
theorem rational_not_fermat_42 {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 2 := by
  intro h
  let A : ℤ := a.num * b.den
  let B : ℤ := b.num * a.den
  let d : ℚ := a.den * b.den
  have hd : d ≠ 0 := by
    dsimp [d]
    exact mul_ne_zero (by exact_mod_cast a.den_nz) (by exact_mod_cast b.den_nz)
  have hA : (A : ℚ) = d * a := by
    dsimp [A, d]
    push_cast
    rw [← Rat.mul_den_eq_num a]
    ring
  have hB : (B : ℚ) = d * b := by
    dsimp [B, d]
    push_cast
    rw [← Rat.mul_den_eq_num b]
    ring
  have hAnz : A ≠ 0 := by
    intro hz
    have hz' : (A : ℚ) = 0 := by rw [hz]; norm_num
    rw [hA] at hz'
    exact mul_ne_zero hd ha hz'
  have hBnz : B ≠ 0 := by
    intro hz
    have hz' : (B : ℚ) = 0 := by rw [hz]; norm_num
    rw [hB] at hz'
    exact mul_ne_zero hd hb hz'
  have hs : IsSquare ((A ^ 4 + B ^ 4 : ℤ) : ℚ) := by
    refine ⟨d ^ 2 * c, ?_⟩
    push_cast
    rw [hA, hB]
    linear_combination d ^ 4 * h
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hs
  apply not_fermat_42 hAnz hBnz
  simpa only [pow_two] using hC

/-- The complete affine rational point set of `y² = x³ - 4x`.
The nonzero-ordinate case gives the forbidden equation
`(y/x)⁴ + 2⁴ = (x + 4/x)²`. -/
theorem small_E2_affine_points {x y : ℚ} (h : y ^ 2 = x ^ 3 - 4 * x) :
    y = 0 ∧ (x = 0 ∨ x = 2 ∨ x = -2) := by
  have hy : y = 0 := by
    by_contra hy
    have hx : x ≠ 0 := by
      intro hx
      rw [hx] at h
      norm_num at h
      exact hy h
    apply rational_not_fermat_42 (a := y / x) (b := 2) (c := x + 4 / x)
      (div_ne_zero hy hx) (by norm_num)
    field_simp
    linear_combination (y ^ 2 + x ^ 3 - 4 * x) * h
  refine ⟨hy, ?_⟩
  have hp : x * (x - 2) * (x + 2) = 0 := by
    rw [hy] at h
    linear_combination -h
  rcases mul_eq_zero.mp hp with hp | hp
  · rcases mul_eq_zero.mp hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-- Both implications of the affine point-list classification. -/
theorem small_E2_affine_iff (x y : ℚ) :
    y ^ 2 = x ^ 3 - 4 * x ↔ y = 0 ∧ (x = 0 ∨ x = 2 ∨ x = -2) := by
  constructor
  · exact small_E2_affine_points
  · rintro ⟨rfl, rfl | rfl | rfl⟩ <;> norm_num

/-- The three listed finite roots are nonsingular on the literal curve. -/
theorem small_E2_root_nonsingular {x : ℚ} (hx : x = 0 ∨ x = 2 ∨ x = -2) :
    (splitCurve 2 (-2)).toAffine.Nonsingular x 0 := by
  rcases hx with rfl | rfl | rfl <;>
    norm_num [WeierstrassCurve.Affine.nonsingular_iff',
      WeierstrassCurve.Affine.equation_iff, splitCurve]

def smallE2ZeroRoot : (splitCurve 2 (-2)).toAffine.Point :=
  .some 0 0 (small_E2_root_nonsingular (Or.inl rfl))

def smallE2PositiveRoot : (splitCurve 2 (-2)).toAffine.Point :=
  .some 2 0 (small_E2_root_nonsingular (Or.inr (Or.inl rfl)))

def smallE2NegativeRoot : (splitCurve 2 (-2)).toAffine.Point :=
  .some (-2) 0 (small_E2_root_nonsingular (Or.inr (Or.inr rfl)))

/-- The complete rational point list includes the point at infinity in
Mathlib's actual elliptic-curve point type. -/
theorem small_E2_point_list (P : (splitCurve 2 (-2)).toAffine.Point) :
    P = 0 ∨ P = smallE2ZeroRoot ∨ P = smallE2PositiveRoot ∨ P = smallE2NegativeRoot := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y hxy =>
    have heq := (splitCurve_equation_iff 2 (-2) x y).mp hxy.1
    have hpoly : y ^ 2 = x ^ 3 - 4 * x := by nlinarith [heq]
    obtain ⟨rfl, hx⟩ := small_E2_affine_points hpoly
    rcases hx with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

/-- Every rational point of the literal curve is killed by two. -/
theorem small_E2_two_torsion (P : (splitCurve 2 (-2)).toAffine.Point) :
    2 • P = 0 := by
  cases P with
  | zero => exact nsmul_zero 2
  | some x y hxy =>
    have heq := (splitCurve_equation_iff 2 (-2) x y).mp hxy.1
    have hy := (small_E2_affine_points (show y ^ 2 = x ^ 3 - 4 * x by nlinarith [heq])).1
    rw [two_nsmul]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [splitCurve, WeierstrassCurve.Affine.negY, hy]

#print axioms rational_not_fermat_42
#print axioms small_E2_affine_points
#print axioms small_E2_affine_iff
#print axioms small_E2_point_list
#print axioms small_E2_two_torsion

end FourCorner
