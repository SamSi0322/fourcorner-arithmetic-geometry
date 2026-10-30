import ChordRestriction
import Mathlib.RingTheory.PowerSeries.Derivative

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman
variable {K : Type*} [Field K]

/-- Differentiate in the second coordinate and then restrict to s=0. -/
def rightDerivative : MvPowerSeries (Unit⊕Unit) K →ₗ[K] PowerSeries K :=
  (substAlgHom (hasSubst_rightZero (K:=K))).toLinearMap.comp (replay_pderiv (Sum.inr ()))

lemma rightDerivative_apply (f : MvPowerSeries (Unit⊕Unit) K) :
    rightDerivative f=rightZeroMap (replay_pderiv (Sum.inr ()) f) := rfl

lemma rightDerivative_mul (f g : MvPowerSeries (Unit⊕Unit) K) :
    rightDerivative (f*g)=rightZeroMap f*rightDerivative g+rightDerivative f*rightZeroMap g := by
  simp only [rightDerivative_apply,pderiv_mul,map_add,map_mul]

@[simp] lemma rightDerivative_C (a : K) : rightDerivative (C a)=0 := by
  rw [rightDerivative_apply,replay_pderiv_C,map_zero]
@[simp] lemma rightDerivative_two : rightDerivative (2:MvPowerSeries (Unit⊕Unit) K)=0 := by
  have hc : (C (2:K) : MvPowerSeries (Unit⊕Unit) K)=2 := map_ofNat _ 2
  rw [← hc]
  exact rightDerivative_C (K:=K) (2:K)
@[simp] lemma rightDerivative_X_left : rightDerivative (X (Sum.inl ()) : MvPowerSeries (Unit⊕Unit) K)=0 := by
  rw [rightDerivative_apply,replay_pderiv_X,if_neg (by decide),map_zero]
@[simp] lemma rightDerivative_X_right : rightDerivative (X (Sum.inr ()) : MvPowerSeries (Unit⊕Unit) K)=1 := by
  rw [rightDerivative_apply,replay_pderiv_X,if_pos rfl,map_one]

lemma rightDerivative_intercept (W : WeierstrassCurve K) :
    rightDerivative W.interceptSeries= -rightZeroMap W.slopeSeries :=
  rightZero_derivative_intercept W

/-- This is the actual differential matrix entry of the actual group law. -/
lemma rightDerivative_addSeries (W : WeierstrassCurve K) :
    rightDerivative W.addSeries=W.formalGroupLaw.diffMatrix () () := by
  rw [rightDerivative_apply,rightZeroMap_apply]
  rfl

/-- Differentiating the exact cleared chord identity gives M*V=2-V, including
all terms of the genuine series. No derivative of an inverse is assumed. -/
theorem short_diffMatrix_mul_v (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    W.formalGroupLaw.diffMatrix () ()*W.vSeries=2-W.vSeries := by
  have h := congrArg (rightDerivative (K:=K)) (short_add_cleared W h1 h2 h3 h6)
  simp only [map_add,rightDerivative_mul,rightDerivative_X_left,rightDerivative_X_right,
    rightDerivative_C,rightDerivative_two,rightDerivative_addSeries,rightDerivative_intercept,
    map_mul,map_ofNat,rightZeroMap_C,rightZeroMap_X_left,rightZeroMap_X_right,
    rightZero_add,rightZero_intercept,rightZero_slope,rightZero_shortChordDenom W h1 h2 h3 h6,
    zero_add,add_zero,zero_mul,mul_zero,one_mul,mul_one] at h
  linear_combination h + 2*(short_v_equation W h1 h2 h3 h6)

/-- Only a unit series is inverted; the nonunit parameter X is never inverted
inside the power-series ring. -/
def shortOmega (W : WeierstrassCurve K) : PowerSeries K :=
  W.vSeries*PowerSeries.invOfUnit (2-W.vSeries) 1

lemma two_sub_v_constant (W : WeierstrassCurve K) : PowerSeries.constantCoeff (2-W.vSeries)=1 := by
  rw [map_sub,W.constantCoeff_vSeries]
  have hc : PowerSeries.constantCoeff (2:PowerSeries K)=(2:K) := map_ofNat _ 2
  rw [hc]
  ring

lemma two_sub_v_mul_inv (W : WeierstrassCurve K) :
    (2-W.vSeries)*PowerSeries.invOfUnit (2-W.vSeries) 1=1 :=
  PowerSeries.mul_invOfUnit _ _ (two_sub_v_constant W)

theorem short_diffMatrix_mul_omega (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    W.formalGroupLaw.diffMatrix () ()*shortOmega W=1 := by
  rw [shortOmega,← mul_assoc,short_diffMatrix_mul_v W h1 h2 h3 h6,two_sub_v_mul_inv]

/-- Identify the entry of the genuine matrix inverse, not a separately chosen
scalar inverse. -/
theorem short_inverseDiffMatrix (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    W.formalGroupLaw.diffMatrix⁻¹ () ()=shortOmega W := by
  have hm := Matrix.nonsing_inv_mul W.formalGroupLaw.diffMatrix
    ((Matrix.isUnit_iff_isUnit_det _).mp W.formalGroupLaw.isUnit_diffMatrix)
  have he := congrArg (fun M => M () ()) hm
  simp only [Matrix.mul_apply,Fintype.sum_unique,Matrix.one_apply_eq] at he
  calc
    W.formalGroupLaw.diffMatrix⁻¹ () ()=
      W.formalGroupLaw.diffMatrix⁻¹ () ()*(W.formalGroupLaw.diffMatrix () ()*shortOmega W) := by
        rw [short_diffMatrix_mul_omega W h1 h2 h3 h6,mul_one]
    _=(W.formalGroupLaw.diffMatrix⁻¹ () ()*W.formalGroupLaw.diffMatrix () ())*shortOmega W := by ring
    _=shortOmega W := by rw [he,one_mul]

/-- Coefficient-wise compatibility with the native univariate derivation. -/
theorem replay_derivative_eq_native (f : PowerSeries K) :
    replay_pderiv () f=PowerSeries.derivative K f := by
  apply PowerSeries.ext
  intro m
  change MvPowerSeries.coeff (Finsupp.single () m) (replay_pderiv () f)=_
  rw [replay_coeff_pderiv,PowerSeries.coeff_derivative,← Finsupp.single_add]
  simp only [Finsupp.single_eq_same,PowerSeries.coeff_coeToMvPowerSeries]
  push_cast
  ring

/-- The canonical formal logarithm differentiates to the actual short-model
invariant differential coefficient. -/
theorem short_log_derivative [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    PowerSeries.derivative K (W.formalGroupLaw.log ())=shortOmega W := by
  rw [← replay_derivative_eq_native,W.formalGroupLaw.pderiv_log,
    short_inverseDiffMatrix W h1 h2 h3 h6]

#print axioms short_diffMatrix_mul_v
#print axioms short_inverseDiffMatrix
#print axioms replay_derivative_eq_native
#print axioms short_log_derivative
end FourCorner.CommonSource.LogPrecision
