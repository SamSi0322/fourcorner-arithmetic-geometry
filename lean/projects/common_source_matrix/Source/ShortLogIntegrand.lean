import ShortInvariantDifferential

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
variable {K : Type*} [Field K]

/-- The exact derivative of the actual unit part, with every denominator
cleared in the power-series ring. -/
theorem short_v_derivative_cleared (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (2-W.vSeries)*PowerSeries.X*(PowerSeries.derivative K W.vSeries)=
      4*W.vSeries*(W.vSeries-1) := by
  have hv := short_v_equation W h1 h2 h3 h6
  have hd := congrArg (PowerSeries.derivative K) hv
  simp only [map_add,Derivation.map_one_eq_zero,Derivation.leibniz,PowerSeries.derivative_C,
    PowerSeries.derivative_X,Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,
    Nat.reduceSub,zero_mul,mul_zero,add_zero,zero_add,one_mul,mul_one] at hd
  linear_combination PowerSeries.X*W.vSeries*hd -
    (2*PowerSeries.X*(PowerSeries.derivative K W.vSeries)+4*W.vSeries)*hv

lemma two_sub_v_ne_zero (W : WeierstrassCurve K) : (2:PowerSeries K)-W.vSeries ≠ 0 := by
  intro h
  have hc := congrArg PowerSeries.constantCoeff h
  rw [two_sub_v_constant,map_zero] at hc
  exact one_ne_zero hc

lemma two_sub_v_mul_omega (W : WeierstrassCurve K) :
    (2-W.vSeries)*shortOmega W=W.vSeries := by
  unfold shortOmega
  linear_combination W.vSeries*(two_sub_v_mul_inv W)

/-- The paper's displayed scalar integrand, proved in a denominator-cleared
form from the actual series, before passage to any fraction field. -/
theorem short_omega_integrand_cleared (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (2*W.vSeries)*shortOmega W=2*W.vSeries+PowerSeries.X*(PowerSeries.derivative K W.vSeries) := by
  apply mul_left_cancel₀ (two_sub_v_ne_zero W)
  linear_combination 2*W.vSeries*(two_sub_v_mul_omega W) -
    short_v_derivative_cleared W h1 h2 h3 h6

/-- The genuine canonical logarithm has exactly the paper's displayed
normalized integrand. Literal geometric dx/(2y) comparison follows separately. -/
theorem short_log_integrand_cleared [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (2*W.vSeries)*PowerSeries.derivative K (W.formalGroupLaw.log ())=
      2*W.vSeries+PowerSeries.X*(PowerSeries.derivative K W.vSeries) := by
  rw [short_log_derivative W h1 h2 h3 h6]
  exact short_omega_integrand_cleared W h1 h2 h3 h6

#print axioms short_v_derivative_cleared
#print axioms short_omega_integrand_cleared
#print axioms short_log_integrand_cleared
end FourCorner.CommonSource.LogPrecision
