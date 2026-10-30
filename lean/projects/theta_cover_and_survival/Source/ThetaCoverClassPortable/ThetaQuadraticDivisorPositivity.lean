import ThetaCoverClassPortable.ThetaQuadraticHalfUnweighted

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open AlgebraicGeometry AlgebraicCurve

namespace FourCorner.ThetaQuadraticDivisorPositivity
open ThetaQuadraticCurve
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsCurveOver F functionField := field_isCurveOver

theorem place_degree_positive (w : Place F functionField) : 0<w.deg := by
  letI : Module.Finite F w.ResidueField := IsCurveOver.finite_residueField w
  exact Module.finrank_pos

/-- Weighted residue degrees are genuinely positive over F; no
algebraically-closed-only degree-one simplification is used. -/
theorem effective_degree_zero_eq_zero (D : Divisor F functionField)
    (hD : 0≤D) (hd : Divisor.degree D=0) : D=0 := by
  have hs : ∑w∈D.support,D w*(w.deg:ℤ)=0 := by
    simpa only [Divisor.degree,Finsupp.liftAddHom_apply,Finsupp.sum,AddMonoidHom.mulRight_apply] using hd
  apply Finsupp.ext
  intro w
  by_cases hw : w∈D.support
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
      mul_nonneg (hD v) (by exact_mod_cast Nat.zero_le v.deg))).mp hs w hw
    have hdeg : (w.deg:ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt (place_degree_positive w))
    exact (mul_eq_zero.mp hz).resolve_right hdeg
  · exact Finsupp.notMem_support_iff.mp hw

end FourCorner.ThetaQuadraticDivisorPositivity
