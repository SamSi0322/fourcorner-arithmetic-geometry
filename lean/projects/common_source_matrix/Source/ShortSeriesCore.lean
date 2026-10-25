import FormalCurveNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman

/-- The literal unit part of the actual formal parameterization satisfies the
short-model equation. No inverse of the nonunit parameter X is taken. -/
theorem short_v_equation {K : Type*} [Field K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    W.vSeries=1+PowerSeries.C W.a₄*PowerSeries.X^4*W.vSeries^2 := by
  have hw := W.wSeries_eq
  simp only [h1,h2,h3,h6,map_zero,zero_mul,mul_zero,add_zero,zero_add] at hw
  rw [W.wSeries_eq_X_pow_three_mul] at hw
  apply mul_left_cancel₀ (pow_ne_zero 3 (PowerSeries.X_ne_zero (R:=K)))
  linear_combination hw

/-- The denominator from the actual chord formula. -/
def shortChordDenom {K : Type*} [Field K] (W : WeierstrassCurve K) :
    MvPowerSeries (Unit⊕Unit) K := 1+C W.a₄*W.slopeSeries^2

lemma shortChordDenom_constant {K : Type*} [Field K] (W : WeierstrassCurve K) :
    constantCoeff (shortChordDenom W)=1 := by simp [shortChordDenom]

/-- Clearing the actual chord denominator before differentiating avoids any
assumed derivative formula for a power-series inverse. -/
theorem short_add_cleared {K : Type*} [Field K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    W.addSeries*shortChordDenom W=
      (X (Sum.inl ())+X (Sum.inr ()))*shortChordDenom W+
        2*C W.a₄*W.slopeSeries*W.interceptSeries := by
  have hi : W.addSeries= -W.thirdRootSeries := by
    rw [WeierstrassCurve.addSeries,short_inverse W h1 h3]
    change subst (fun _ : Unit => W.thirdRootSeries) (-(X () : MvPowerSeries Unit K))= _
    rw [← substAlgHom_apply W.hasSubst_thirdRootSeries,map_neg,
      substAlgHom_apply,subst_X W.hasSubst_thirdRootSeries]
  have hD : shortChordDenom W * invOfUnit (shortChordDenom W) 1=1 :=
    MvPowerSeries.mul_invOfUnit _ _ (shortChordDenom_constant W)
  rw [hi,WeierstrassCurve.thirdRootSeries]
  simp only [h1,h2,h3,h6,map_zero,zero_mul,mul_zero,add_zero,zero_add]
  change (-(-X (Sum.inl ())-X (Sum.inr ())-
    (2*C W.a₄*W.slopeSeries*W.interceptSeries)*invOfUnit (shortChordDenom W) 1))*
    shortChordDenom W=(X (Sum.inl ())+X (Sum.inr ()))*shortChordDenom W+
      2*C W.a₄*W.slopeSeries*W.interceptSeries
  linear_combination (2*C W.a₄*W.slopeSeries*W.interceptSeries)*hD

#print axioms short_v_equation
#print axioms short_add_cleared
end FourCorner.CommonSource.LogPrecision
