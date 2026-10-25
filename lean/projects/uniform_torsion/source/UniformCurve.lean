import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The integral pair-parameter curve and an explicit point of order four in
Mathlib's actual affine point group. -/

namespace FourCorner.UniformTorsion

def alpha (mu nu : ℤ) : ℤ := 2 * (3 * mu ^ 2 - 4 * nu ^ 2)

def B (mu nu : ℤ) : ℤ := 4 * nu ^ 2 - mu ^ 2

def curve (mu nu : ℤ) : WeierstrassCurve ℚ :=
  ⟨0, (alpha mu nu : ℚ), 0, (B mu nu : ℚ) ^ 2, 0⟩

theorem alpha_add_two_B (mu nu : ℤ) :
    (alpha mu nu : ℚ) + 2 * (B mu nu : ℚ) = 4 * (mu : ℚ) ^ 2 := by
  simp only [alpha, B, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  ring

theorem curve_equation_iff (mu nu : ℤ) (x y : ℚ) :
    (curve mu nu).toAffine.Equation x y ↔
      y ^ 2 = x ^ 3 + (alpha mu nu : ℚ) * x ^ 2 + (B mu nu : ℚ) ^ 2 * x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve, zero_mul, add_zero]

theorem zero_nonsingular {mu nu : ℤ} (hB : B mu nu ≠ 0) :
    (curve mu nu).toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  simpa [curve] using (show (B mu nu : ℚ) ≠ 0 by exact_mod_cast hB)

theorem orderFour_equation (mu nu : ℤ) :
    (curve mu nu).toAffine.Equation (B mu nu : ℚ)
      (2 * (mu : ℚ) * (B mu nu : ℚ)) := by
  rw [curve_equation_iff]
  calc
    (2 * (mu : ℚ) * (B mu nu : ℚ)) ^ 2 =
        (4 * (mu : ℚ) ^ 2) * (B mu nu : ℚ) ^ 2 := by ring
    _ = ((alpha mu nu : ℚ) + 2 * (B mu nu : ℚ)) * (B mu nu : ℚ) ^ 2 := by
      rw [alpha_add_two_B]
    _ = _ := by ring

theorem orderFour_y_ne_zero {mu nu : ℤ} (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    2 * (mu : ℚ) * (B mu nu : ℚ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hmu))
    (by exact_mod_cast hB)

theorem orderFour_nonsingular {mu nu : ℤ} (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    (curve mu nu).toAffine.Nonsingular (B mu nu : ℚ)
      (2 * (mu : ℚ) * (B mu nu : ℚ)) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  refine ⟨orderFour_equation mu nu, Or.inr ?_⟩
  simpa [curve] using (mul_ne_zero (show (2 : ℚ) ≠ 0 by norm_num)
    (orderFour_y_ne_zero hmu hB))

def zeroPoint (mu nu : ℤ) (hB : B mu nu ≠ 0) : (curve mu nu).toAffine.Point :=
  .some 0 0 (zero_nonsingular hB)

def orderFourPoint (mu nu : ℤ) (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    (curve mu nu).toAffine.Point :=
  .some (B mu nu : ℚ) (2 * (mu : ℚ) * (B mu nu : ℚ)) (orderFour_nonsingular hmu hB)

theorem zeroPoint_ne_zero (mu nu : ℤ) (hB : B mu nu ≠ 0) : zeroPoint mu nu hB ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

theorem zeroPoint_add_self (mu nu : ℤ) (hB : B mu nu ≠ 0) :
    zeroPoint mu nu hB + zeroPoint mu nu hB = 0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [curve, WeierstrassCurve.Affine.negY]

theorem orderFour_y_ne_negY {mu nu : ℤ} (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    2 * (mu : ℚ) * (B mu nu : ℚ) ≠ (curve mu nu).toAffine.negY (B mu nu : ℚ)
      (2 * (mu : ℚ) * (B mu nu : ℚ)) := by
  simp only [curve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
  intro h
  exact orderFour_y_ne_zero hmu hB (by linarith)

theorem orderFour_slope {mu nu : ℤ} (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    (curve mu nu).toAffine.slope (B mu nu : ℚ) (B mu nu : ℚ)
      (2 * (mu : ℚ) * (B mu nu : ℚ)) (2 * (mu : ℚ) * (B mu nu : ℚ)) =
      2 * (mu : ℚ) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (orderFour_y_ne_negY hmu hB)]
  simp only [curve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
  apply (div_eq_iff (show 2 * (mu : ℚ) * (B mu nu : ℚ) -
      -(2 * (mu : ℚ) * (B mu nu : ℚ)) ≠ 0 from
    fun h => orderFour_y_ne_zero hmu hB (by linarith))).mpr
  nlinarith [congrArg (fun a : ℚ => a * (2 * (B mu nu : ℚ))) (alpha_add_two_B mu nu)]

/-- The explicit point doubles to the nonzero point `(0,0)` under Mathlib's
actual affine group operation. -/
theorem orderFourPoint_add_self (mu nu : ℤ) (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    orderFourPoint mu nu hmu hB + orderFourPoint mu nu hmu hB = zeroPoint mu nu hB := by
  have hx : (curve mu nu).toAffine.addX (B mu nu : ℚ) (B mu nu : ℚ)
      ((curve mu nu).toAffine.slope (B mu nu : ℚ) (B mu nu : ℚ)
        (2 * (mu : ℚ) * (B mu nu : ℚ)) (2 * (mu : ℚ) * (B mu nu : ℚ))) = 0 := by
    rw [orderFour_slope hmu hB]
    simp only [WeierstrassCurve.Affine.addX, curve, zero_mul, add_zero]
    nlinarith [alpha_add_two_B mu nu]
  have hy : (curve mu nu).toAffine.addY (B mu nu : ℚ) (B mu nu : ℚ)
      (2 * (mu : ℚ) * (B mu nu : ℚ))
      ((curve mu nu).toAffine.slope (B mu nu : ℚ) (B mu nu : ℚ)
        (2 * (mu : ℚ) * (B mu nu : ℚ)) (2 * (mu : ℚ) * (B mu nu : ℚ))) = 0 := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, hx,
      orderFour_slope hmu hB]
    simp [curve, WeierstrassCurve.Affine.negY]
  unfold orderFourPoint zeroPoint
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (orderFour_y_ne_negY hmu hB)]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

theorem orderFourPoint_two_nsmul_ne_zero (mu nu : ℤ) (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    2 • orderFourPoint mu nu hmu hB ≠ 0 := by
  simpa only [two_nsmul, orderFourPoint_add_self] using zeroPoint_ne_zero mu nu hB

theorem orderFourPoint_four_nsmul (mu nu : ℤ) (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    4 • orderFourPoint mu nu hmu hB = 0 := by
  change (2 + 2) • orderFourPoint mu nu hmu hB = 0
  rw [add_nsmul, two_nsmul, orderFourPoint_add_self, zeroPoint_add_self]

/-- The displayed point has exact order four, not merely order dividing four. -/
theorem orderFourPoint_addOrderOf (mu nu : ℤ) (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    addOrderOf (orderFourPoint mu nu hmu hB) = 4 := by
  apply addOrderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one] using orderFourPoint_two_nsmul_ne_zero mu nu hmu hB
  · exact orderFourPoint_four_nsmul mu nu hmu hB

theorem exists_order_four (mu nu : ℤ) (hmu : mu ≠ 0) (hB : B mu nu ≠ 0) :
    ∃ P : (curve mu nu).toAffine.Point, addOrderOf P = 4 :=
  ⟨orderFourPoint mu nu hmu hB, orderFourPoint_addOrderOf mu nu hmu hB⟩

end FourCorner.UniformTorsion

#print axioms FourCorner.UniformTorsion.zero_nonsingular
#print axioms FourCorner.UniformTorsion.orderFour_nonsingular
#print axioms FourCorner.UniformTorsion.orderFourPoint_add_self
#print axioms FourCorner.UniformTorsion.orderFourPoint_addOrderOf
#print axioms FourCorner.UniformTorsion.exists_order_four
