import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The actual affine group law on a split cubic identifies nonzero
three-torsion points with rational tangent flexes. -/

namespace FourCorner

/-- The split cubic `y² = x(x-A)(x-B)` as an actual Weierstrass curve. -/
def splitCurve (A B : ℚ) : WeierstrassCurve ℚ :=
  ⟨0, -(A + B), 0, A * B, 0⟩

theorem splitCurve_discriminant (A B : ℚ) :
    (splitCurve A B).Δ = 16 * A ^ 2 * B ^ 2 * (A - B) ^ 2 := by
  simp only [splitCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem splitCurve_discriminant_ne_zero_iff (A B : ℚ) :
    (splitCurve A B).Δ ≠ 0 ↔ A ≠ 0 ∧ B ≠ 0 ∧ A ≠ B := by
  rw [splitCurve_discriminant]
  norm_num [mul_ne_zero_iff, sub_eq_zero, and_assoc]

theorem splitCurve_equation_iff (A B x y : ℚ) :
    (splitCurve A B).toAffine.Equation x y ↔ y ^ 2 = x * (x - A) * (x - B) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [splitCurve, zero_mul, add_zero]
  constructor <;> intro h <;> nlinarith [h]

/-- Three-torsion in Mathlib's actual point group gives the equality
`P + P = -P`. -/
theorem affine_three_torsion_double_eq_neg {W : WeierstrassCurve.Affine ℚ}
    (P : W.Point) (h3 : 3 • P = 0) : P + P = -P := by
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [three'_nsmul] using h3

/-- A finite three-torsion point has a nonvertical tangent, and Mathlib's
doubling abscissa equals its original abscissa. -/
theorem affine_three_torsion_addX {W : WeierstrassCurve.Affine ℚ} {x y : ℚ}
    (hxy : W.Nonsingular x y)
    (h3 : 3 • WeierstrassCurve.Affine.Point.some x y hxy = 0) :
    y ≠ W.negY x y ∧ W.addX x x (W.slope x x y y) = x := by
  have hdbl := affine_three_torsion_double_eq_neg _ h3
  have hy : y ≠ W.negY x y := by
    intro heq
    have htwo : WeierstrassCurve.Affine.Point.some x y hxy +
        WeierstrassCurve.Affine.Point.some x y hxy = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq heq
    have hneg : -WeierstrassCurve.Affine.Point.some x y hxy = 0 := hdbl.symm.trans htwo
    exact WeierstrassCurve.Affine.Point.some_ne_zero hxy (neg_eq_zero.mp hneg)
  refine ⟨hy, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy,
    WeierstrassCurve.Affine.Point.neg_some] at hdbl
  exact (WeierstrassCurve.Affine.Point.some.inj hdbl).1

/-- When the doubling formula returns the original abscissa, the tangent
intersection polynomial is a cube. -/
theorem splitCurve_tangent_identity_of_addX_eq {A B x y : ℚ}
    (hxy : (splitCurve A B).toAffine.Nonsingular x y)
    (hy : y ≠ (splitCurve A B).toAffine.negY x y)
    (hx : (splitCurve A B).toAffine.addX x x
      ((splitCurve A B).toAffine.slope x x y y) = x) :
    ∀ z : ℚ, z * (z - A) * (z - B) -
      ((splitCurve A B).toAffine.slope x x y y * (z - x) + y) ^ 2 = (z - x) ^ 3 := by
  intro z
  have hpoly := (splitCurve A B).toAffine.addPolynomial_slope hxy.1 hxy.1
    (fun h => hy h.2)
  rw [hx] at hpoly
  have heval := congrArg (Polynomial.eval z) hpoly
  simp [WeierstrassCurve.Affine.addPolynomial, WeierstrassCurve.Affine.polynomial,
    WeierstrassCurve.Affine.linePolynomial, splitCurve] at heval
  simp only [splitCurve, neg_add_rev]
  nlinarith [heval]

/-- The tangent at an actual finite three-torsion point of the split cubic has
triple contact. Its slope is Mathlib's tangent slope, not an assumed flex datum. -/
theorem splitCurve_three_torsion_some_tangent {A B x y : ℚ}
    (hxy : (splitCurve A B).toAffine.Nonsingular x y)
    (h3 : 3 • WeierstrassCurve.Affine.Point.some x y hxy = 0) :
    y ≠ 0 ∧ y ^ 2 = x * (x - A) * (x - B) ∧
      ∀ z : ℚ, z * (z - A) * (z - B) -
        ((splitCurve A B).toAffine.slope x x y y * (z - x) + y) ^ 2 = (z - x) ^ 3 := by
  obtain ⟨hy, hx⟩ := affine_three_torsion_addX hxy h3
  refine ⟨?_, (splitCurve_equation_iff A B x y).mp hxy.1,
    splitCurve_tangent_identity_of_addX_eq hxy hy hx⟩
  intro heq
  apply hy
  simp [splitCurve, WeierstrassCurve.toAffine, WeierstrassCurve.Affine.negY, heq]

/-- Every nonzero actual three-torsion point provides a rational tangent flex
on the split cubic. No division-polynomial or flex assumption is required. -/
theorem splitCurve_three_torsion_tangent {A B : ℚ}
    (P : (splitCurve A B).toAffine.Point) (hP : P ≠ 0) (h3 : 3 • P = 0) :
    ∃ x y m : ℚ, y ≠ 0 ∧ y ^ 2 = x * (x - A) * (x - B) ∧
      ∀ z : ℚ, z * (z - A) * (z - B) - (m * (z - x) + y) ^ 2 = (z - x) ^ 3 := by
  cases P with
  | zero => exact (hP rfl).elim
  | some x y hxy =>
      exact ⟨x, y, (splitCurve A B).toAffine.slope x x y y,
        splitCurve_three_torsion_some_tangent hxy h3⟩

end FourCorner

#print axioms FourCorner.splitCurve_discriminant
#print axioms FourCorner.splitCurve_discriminant_ne_zero_iff
#print axioms FourCorner.affine_three_torsion_addX
#print axioms FourCorner.splitCurve_three_torsion_some_tangent
#print axioms FourCorner.splitCurve_three_torsion_tangent
