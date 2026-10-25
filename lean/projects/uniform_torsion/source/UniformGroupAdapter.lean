import UniformCurve
import UniformDoubling

namespace FourCorner.UniformTorsion

/-- The actual family inherits the uniform square-abscissa doubling identity. -/
theorem curve_any_double_square {mu nu : ℤ} {X Y : ℚ}
    (P : (curve mu nu).toAffine.Point)
    (hXY : (curve mu nu).toAffine.Nonsingular X Y)
    (hdouble : 2 • P = WeierstrassCurve.Affine.Point.some X Y hXY) :
    ∃ r : ℚ, X=r^2 :=
  quadraticTail_any_double_square P hXY hdouble

/-- Literal rational translation by the actual visible two-torsion point. -/
theorem curve_translate_zero {mu nu : ℤ} {x y : ℚ}
    (hB : B mu nu ≠ 0)
    (hxy : (curve mu nu).toAffine.Nonsingular x y) (hx : x ≠ 0) :
    ∃ hN : (curve mu nu).toAffine.Nonsingular
      ((B mu nu : ℚ)^2/x) (-(B mu nu : ℚ)^2*y/x^2),
      WeierstrassCurve.Affine.Point.some x y hxy + zeroPoint mu nu hB =
        WeierstrassCurve.Affine.Point.some ((B mu nu : ℚ)^2/x)
          (-(B mu nu : ℚ)^2*y/x^2) hN :=
  quadraticTail_translate_zero hxy (zero_nonsingular hB) hx

/-- A nonsquare B excludes halves of either ordinate over abscissa B. -/
theorem curve_no_half_at_B {mu nu : ℤ} {Y : ℚ}
    (hB : ¬∃ r : ℚ, (B mu nu : ℚ)=r^2)
    (hXY : (curve mu nu).toAffine.Nonsingular (B mu nu : ℚ) Y) :
    ¬∃ P : (curve mu nu).toAffine.Point,
      2 • P = WeierstrassCurve.Affine.Point.some (B mu nu : ℚ) Y hXY :=
  quadraticTail_no_half hB hXY

#print axioms curve_any_double_square
#print axioms curve_translate_zero
#print axioms curve_no_half_at_B
end FourCorner.UniformTorsion
