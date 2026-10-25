import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace FourCorner.UniformTorsion

/-- The zero-constant Weierstrass model whose linear coefficient is a square. -/
def quadraticTailCurve {K : Type*} [Field K] (a b : K) : WeierstrassCurve K :=
  ⟨0, a, 0, b^2, 0⟩

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K] {a b x y : K}

theorem quadraticTail_equation_iff :
    (quadraticTailCurve a b).toAffine.Equation x y ↔ y^2=x^3+a*x^2+b^2*x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [quadraticTailCurve]

/-- The exact duplication abscissa, in square form over the coefficient field. -/
theorem quadraticTail_double_x (hxy : (quadraticTailCurve a b).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    (quadraticTailCurve a b).toAffine.addX x x
      ((quadraticTailCurve a b).toAffine.slope x x y y) = ((x^2-b^2)/(2*y))^2 := by
  have hneg : y ≠ (quadraticTailCurve a b).toAffine.negY x y := by
    simp only [WeierstrassCurve.Affine.negY, quadraticTailCurve, zero_mul, sub_zero]
    intro he
    have hz : 2*y=0 := by linear_combination he
    exact hy ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp only [quadraticTailCurve, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, zero_mul, sub_zero, add_zero, sub_neg_eq_add]
  have he := quadraticTail_equation_iff.mp hxy.1
  field_simp
  linear_combination -16*(a+2*x)*he

/-- A finite actual double has square abscissa. This includes the group-law bridge. -/
theorem quadraticTail_double_square {X Y : K}
    (hxy : (quadraticTailCurve a b).toAffine.Nonsingular x y)
    (hXY : (quadraticTailCurve a b).toAffine.Nonsingular X Y)
    (hdouble : 2 • WeierstrassCurve.Affine.Point.some x y hxy =
      WeierstrassCurve.Affine.Point.some X Y hXY) : ∃ r : K, X=r^2 := by
  have hy : y ≠ 0 := by
    intro hz
    have hh : y = (quadraticTailCurve a b).toAffine.negY x y := by
      simp [quadraticTailCurve, WeierstrassCurve.Affine.negY, hz]
    have hzero := WeierstrassCurve.Affine.Point.add_self_of_Y_eq (h₁:=hxy) hh
    rw [two_nsmul, hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hXY hdouble.symm
  have hneg : y ≠ (quadraticTailCurve a b).toAffine.negY x y := by
    simp only [WeierstrassCurve.Affine.negY, quadraticTailCurve, zero_mul, sub_zero]
    intro he
    have hz : 2*y=0 := by linear_combination he
    exact hy ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg] at hdouble
  have hx := (WeierstrassCurve.Affine.Point.some.inj hdouble).1
  exact ⟨(x^2-b^2)/(2*y), hx.symm.trans (quadraticTail_double_x hxy hy)⟩

/-- Every double that lands at a finite actual point has a square first coordinate. -/
theorem quadraticTail_any_double_square {X Y : K}
    (P : (quadraticTailCurve a b).toAffine.Point)
    (hXY : (quadraticTailCurve a b).toAffine.Nonsingular X Y)
    (hdouble : 2 • P = WeierstrassCurve.Affine.Point.some X Y hXY) : ∃ r : K, X=r^2 := by
  cases P with
  | zero =>
      change 2 • (0 : (quadraticTailCurve a b).toAffine.Point) = _ at hdouble
      rw [smul_zero] at hdouble
      have hz := hdouble
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hXY hz.symm).elim
  | some x y hxy => exact quadraticTail_double_square hxy hXY hdouble

/-- No point with a nonsquare abscissa is a double in the actual point group. -/
theorem quadraticTail_no_half {X Y : K}
    (hX : ¬∃ r : K, X=r^2)
    (hXY : (quadraticTailCurve a b).toAffine.Nonsingular X Y) :
    ¬∃ P : (quadraticTailCurve a b).toAffine.Point,
      2 • P = WeierstrassCurve.Affine.Point.some X Y hXY := by
  rintro ⟨P,hP⟩
  exact hX (quadraticTail_any_double_square P hXY hP)

/-- Translation by the visible two-torsion point in exact affine coordinates. -/
theorem quadraticTail_translate_zero {a b x y : K}
    (hxy : (quadraticTailCurve a b).toAffine.Nonsingular x y)
    (hzero : (quadraticTailCurve a b).toAffine.Nonsingular 0 0)
    (hx : x ≠ 0) :
    ∃ hN : (quadraticTailCurve a b).toAffine.Nonsingular (b^2/x) (-b^2*y/x^2),
      WeierstrassCurve.Affine.Point.some x y hxy +
        WeierstrassCurve.Affine.Point.some 0 0 hzero =
          WeierstrassCurve.Affine.Point.some (b^2/x) (-b^2*y/x^2) hN := by
  have he := quadraticTail_equation_iff.mp hxy.1
  have hX : (quadraticTailCurve a b).toAffine.addX x 0
      ((quadraticTailCurve a b).toAffine.slope x 0 y 0) = b^2/x := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    simp only [WeierstrassCurve.Affine.addX, quadraticTailCurve, zero_mul, add_zero, sub_zero]
    field_simp
    linear_combination he
  have hY : (quadraticTailCurve a b).toAffine.addY x 0 y
      ((quadraticTailCurve a b).toAffine.slope x 0 y 0) = -b^2*y/x^2 := by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    rw [hX, WeierstrassCurve.Affine.slope_of_X_ne hx]
    simp only [WeierstrassCurve.Affine.negY, quadraticTailCurve, zero_mul, sub_zero]
    field_simp
    <;> ring
  have hN := (quadraticTailCurve a b).toAffine.nonsingular_add hxy hzero
    (fun h => hx h.1)
  rw [hX, hY] at hN
  refine ⟨hN, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  simp only [hX, hY]

/-- The visible zero-coordinate point doubles to the group identity. -/
theorem quadraticTail_zero_double
    (hzero : (quadraticTailCurve a b).toAffine.Nonsingular 0 0) :
    2 • WeierstrassCurve.Affine.Point.some 0 0 hzero = 0 := by
  rw [two_nsmul]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  simp [quadraticTailCurve, WeierstrassCurve.Affine.negY]

/-- The two possible abscissas of a finite half of the visible two-torsion point. -/
theorem quadraticTail_half_zero_abscissa
    (hxy : (quadraticTailCurve a b).toAffine.Nonsingular x y)
    (hzero : (quadraticTailCurve a b).toAffine.Nonsingular 0 0)
    (hd : 2 • WeierstrassCurve.Affine.Point.some x y hxy =
      WeierstrassCurve.Affine.Point.some 0 0 hzero) : x=b ∨ x= -b := by
  have hy : y ≠ 0 := by
    intro hz
    have hh : y = (quadraticTailCurve a b).toAffine.negY x y := by
      simp [quadraticTailCurve, WeierstrassCurve.Affine.negY, hz]
    have hz := WeierstrassCurve.Affine.Point.add_self_of_Y_eq (h₁:=hxy) hh
    rw [two_nsmul, hz] at hd
    exact WeierstrassCurve.Affine.Point.some_ne_zero hzero hd.symm
  have hneg : y ≠ (quadraticTailCurve a b).toAffine.negY x y := by
    simp only [WeierstrassCurve.Affine.negY, quadraticTailCurve, zero_mul, sub_zero]
    intro he
    have hz : 2*y=0 := by linear_combination he
    exact hy ((mul_eq_zero.mp hz).resolve_left (by norm_num))
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg] at hd
  have hx := (WeierstrassCurve.Affine.Point.some.inj hd).1
  rw [quadraticTail_double_x hxy hy] at hx
  have hz := sq_eq_zero_iff.mp hx
  have hnum : x^2-b^2=0 := (div_eq_zero_iff.mp hz).resolve_right
    (mul_ne_zero (by norm_num) hy)
  have hp : (x-b)*(x+b)=0 := by linear_combination hnum
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

/-- If neither b nor -b is a square, the visible two-torsion point is not a quadruple. -/
theorem quadraticTail_no_quadruple_zero
    (hzero : (quadraticTailCurve a b).toAffine.Nonsingular 0 0)
    (hb : ¬∃r:K,b=r^2) (hnb : ¬∃r:K,-b=r^2) :
    ¬∃ P : (quadraticTailCurve a b).toAffine.Point,
      4 • P = WeierstrassCurve.Affine.Point.some 0 0 hzero := by
  rintro ⟨P,hP⟩
  have hd : 2 • (2 • P) = WeierstrassCurve.Affine.Point.some 0 0 hzero := by
    rw [←mul_nsmul]
    exact hP
  generalize hQ : 2 • P = Q at hd
  cases Q with
  | zero =>
      change 2 • (0 : (quadraticTailCurve a b).toAffine.Point) = _ at hd
      rw [smul_zero] at hd
      exact WeierstrassCurve.Affine.Point.some_ne_zero hzero hd.symm
  | some x y hxy =>
      obtain ⟨r,hr⟩ := quadraticTail_any_double_square P hxy hQ
      rcases quadraticTail_half_zero_abscissa hxy hzero hd with hx | hx
      · exact hb ⟨r,hx.symm.trans hr⟩
      · exact hnb ⟨r,hx.symm.trans hr⟩

#print axioms quadraticTail_half_zero_abscissa
#print axioms quadraticTail_no_quadruple_zero
#print axioms quadraticTail_translate_zero
#print axioms quadraticTail_zero_double
#print axioms quadraticTail_double_x
#print axioms quadraticTail_double_square
#print axioms quadraticTail_any_double_square
#print axioms quadraticTail_no_half
end FourCorner.UniformTorsion
