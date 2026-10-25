import UniformGroupAdapter
import UniformNonsingular
import UniformDyadicFamily
import UniformLocalBridge

namespace FourCorner.UniformTorsion

/-- The literal integral model for the rational pair-parameter family. -/
def integralCurve (mu nu : ℤ) : WeierstrassCurve ℤ :=
  ⟨0, alpha mu nu, 0, B mu nu ^ 2, 0⟩

theorem integralCurve_map (mu nu : ℤ) :
    (integralCurve mu nu).map (algebraMap ℤ ℚ) = curve mu nu := by
  ext <;> simp [integralCurve, curve, WeierstrassCurve.map]


/-- A nonvertical actual double has the displayed affine abscissa. -/
theorem curve_double_exists {mu nu : ℤ} {x y : ℚ}
    (hxy : (curve mu nu).toAffine.Nonsingular x y) (hy : y ≠ 0) :
    ∃ (Y : ℚ) (hN : (curve mu nu).toAffine.Nonsingular
        (((x^2-(B mu nu : ℚ)^2)/(2*y))^2) Y),
      2 • WeierstrassCurve.Affine.Point.some x y hxy =
        WeierstrassCurve.Affine.Point.some (((x^2-(B mu nu : ℚ)^2)/(2*y))^2) Y hN := by
  have hneg : y ≠ (curve mu nu).toAffine.negY x y := by
    simp only [curve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
    intro hh
    exact hy (by linarith)
  have hX : (curve mu nu).toAffine.addX x x
      ((curve mu nu).toAffine.slope x x y y) =
      ((x^2-(B mu nu : ℚ)^2)/(2*y))^2 := quadraticTail_double_x hxy hy
  let Y := (curve mu nu).toAffine.addY x x y ((curve mu nu).toAffine.slope x x y y)
  have hN := (curve mu nu).toAffine.nonsingular_add hxy hxy (fun h => hneg h.2)
  rw [hX] at hN
  refine ⟨Y, hN, ?_⟩
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hX, rfl⟩

/-- Every fourth multiple is infinity or an actual rational point with a
strict dyadic pole. No bounded search or torsion assumption is used. -/
theorem four_zero_or_pole {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu)
    (P : (curve mu nu).toAffine.Point) :
    4 • P = 0 ∨ ∃ (x y : ℚ) (h : (curve mu nu).toAffine.Nonsingular x y),
      4 • P = WeierstrassCurve.Affine.Point.some x y h ∧ padicValRat 2 x ≤ -2 := by
  generalize hQ : 2 • P = Q
  cases Q with
  | zero =>
    left
    calc 4 • P = 2 • (2 • P) := by simp [← mul_nsmul]
         _ = 0 := by rw [hQ]; change 2 • (0 : (curve mu nu).toAffine.Point) = 0; simp
  | some x y hxy =>
    have hxsq := curve_any_double_square P hxy hQ
    have heq := (curve_equation_iff mu nu x y).mp hxy.1
    rcases family_square_x_dyadic_cases hm hn hxsq heq with hzero | hgood
    · rcases hzero with ⟨rfl, rfl⟩
      left
      calc 4 • P = 2 • (2 • P) := by simp [← mul_nsmul]
           _ = 0 := by rw [hQ]; exact quadraticTail_zero_double hxy
    · obtain ⟨hx, hy, hdup, hval⟩ := hgood
      obtain ⟨Y, hN, hdouble⟩ := curve_double_exists hxy hy
      right
      refine ⟨_, Y, hN, ?_, by omega⟩
      calc 4 • P = 2 • (2 • P) := by simp [← mul_nsmul]
           _ = _ := by rw [hQ]; exact hdouble

/-- The odd-parameter rational point group has no nonzero odd torsion. -/
theorem no_odd_torsion {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu)
    (n : ℕ) (hodd : Odd n) (P : (curve mu nu).toAffine.Point)
    (hkill : n • P = 0) : P = 0 := by
  let : (curve mu nu).IsElliptic := curve_isElliptic hm hn
  exact LocalBridge.eq_zero_of_odd_of_four_zero_or_pole
    (integralCurve_map mu nu) hodd hkill (four_zero_or_pole hm hn P)

#print axioms curve_double_exists
#print axioms four_zero_or_pole
#print axioms no_odd_torsion
end FourCorner.UniformTorsion
