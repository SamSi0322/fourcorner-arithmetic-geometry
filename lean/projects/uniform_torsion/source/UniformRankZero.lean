import UniformTorsion
import EllipticCurves.MordellWeil
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-! Rank zero means actual integer-module finrank zero. Mordell–Weil supplies
the finite-generation hypothesis needed to infer that every point is torsion. -/

namespace FourCorner.UniformTorsion

/-- Genuine rank zero of the actual Weierstrass point group over a number
field implies finite additive order for every point. Finite generation is
supplied by the accepted Mordell–Weil theorem, not assumed. -/
theorem numberField_isOfFinAddOrder_of_finrank_zero {K : Type*} [Field K]
    [NumberField K] [DecidableEq K] (W : WeierstrassCurve.Affine K)
    [W.IsElliptic] (hRank : Module.finrank ℤ W.Point = 0) (P : W.Point) :
    IsOfFinAddOrder P := by
  have hfg : AddGroup.FG W.Point := WeierstrassCurve.Affine.fg_point_of_numberField
  letI : Module.Finite ℤ W.Point := Module.Finite.iff_addGroup_fg.mpr hfg
  have ht : Module.IsTorsion ℤ W.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ) (M := W.Point)).mp hRank
  exact (isAddTorsion_iff_isTorsion_int.mpr ht) P

/-- Under genuine rank zero, all rational points in the odd-parameter family
are among the four previously classified torsion points. -/
theorem rank_zero_point_classification {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu)
    (hRank : Module.finrank ℤ (curve mu nu).toAffine.Point = 0)
    (P : (curve mu nu).toAffine.Point) :
    P = 0 ∨ P = zeroPoint mu nu (B_ne_zero hm) ∨
      P = torsionGenerator mu nu hm ∨ P = -torsionGenerator mu nu hm := by
  letI := curve_isElliptic hm hn
  exact rational_torsion_classification hm hn
    (numberField_isOfFinAddOrder_of_finrank_zero (curve mu nu).toAffine hRank P)

/-- No actual affine point can have its x-coordinate in the strict quotient
interval when the actual rational point group has integer-module rank zero. -/
theorem rank_zero_no_point_between {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu)
    (hRank : Module.finrank ℤ (curve mu nu).toAffine.Point = 0)
    {x y : ℚ} (hxy : (curve mu nu).toAffine.Nonsingular x y)
    (hx : 0 < x) (hxB : x < (B mu nu : ℚ)) : False := by
  letI := curve_isElliptic hm hn
  exact point_between_nontorsion hm hn hxy hx hxB
    (numberField_isOfFinAddOrder_of_finrank_zero (curve mu nu).toAffine hRank
      (WeierstrassCurve.Affine.Point.some x y hxy))

/-- Equation-level interval exclusion, with nonsingularity derived from the
odd parameters rather than required as an extra input. -/
theorem rank_zero_no_equation_between {mu nu : ℤ} (hm : Odd mu) (hn : Odd nu)
    (hRank : Module.finrank ℤ (curve mu nu).toAffine.Point = 0) :
    ¬ ∃ x y : ℚ, (curve mu nu).toAffine.Equation x y ∧
      0 < x ∧ x < (B mu nu : ℚ) := by
  letI := curve_isElliptic hm hn
  rintro ⟨x, y, hxy, hx, hxB⟩
  exact rank_zero_no_point_between hm hn hRank
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp hxy) hx hxB

#print axioms numberField_isOfFinAddOrder_of_finrank_zero
#print axioms rank_zero_point_classification
#print axioms rank_zero_no_point_between
#print axioms rank_zero_no_equation_between

end FourCorner.UniformTorsion
