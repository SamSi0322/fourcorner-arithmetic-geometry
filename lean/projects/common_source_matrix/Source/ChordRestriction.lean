import ShortSeriesCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman

variable {K : Type*} [Field K]

def rightZero : Unit⊕Unit → PowerSeries K := Sum.elim MvPowerSeries.X (fun _ => 0)

lemma hasSubst_rightZero : HasSubst (rightZero (K:=K)) := by
  apply hasSubst_of_constantCoeff_zero
  intro s
  cases s <;> simp [rightZero]

/-- Actual substitution s=0, as a ring map on the two-variable series ring. -/
def rightZeroMap : MvPowerSeries (Unit⊕Unit) K →+* PowerSeries K :=
  (substAlgHom (hasSubst_rightZero (K:=K))).toRingHom

lemma rightZeroMap_apply (f : MvPowerSeries (Unit⊕Unit) K) :
    rightZeroMap f=subst (rightZero (K:=K)) f := substAlgHom_apply hasSubst_rightZero f

@[simp] lemma rightZeroMap_X_left : rightZeroMap (X (Sum.inl ()) : MvPowerSeries (Unit⊕Unit) K)=PowerSeries.X := by
  rw [rightZeroMap_apply,subst_X hasSubst_rightZero]
  rfl
@[simp] lemma rightZeroMap_X_right : rightZeroMap (X (Sum.inr ()) : MvPowerSeries (Unit⊕Unit) K)=0 := by
  rw [rightZeroMap_apply,subst_X hasSubst_rightZero]
  rfl
@[simp] lemma rightZeroMap_C (a : K) : rightZeroMap (C a)=PowerSeries.C a :=
  (substAlgHom (hasSubst_rightZero (K:=K))).commutes a

lemma rightZeroMap_rename_left (f : PowerSeries K) :
    rightZeroMap (rename (fun _ : Unit => Sum.inl ()) f)=f := by
  rw [rightZeroMap_apply,rename_eq_subst,
    subst_comp_subst_apply (HasSubst.X_comp _) hasSubst_rightZero]
  simp only [Function.comp_apply]
  have hh : (fun u : Unit => subst (rightZero (K:=K))
      (X (Sum.inl ()) : MvPowerSeries (Unit⊕Unit) K))=(X : Unit → PowerSeries K) := by
    funext u
    rw [subst_X hasSubst_rightZero]
    cases u
    rfl
  rw [hh,subst_self]
  rfl

lemma rightZeroMap_rename_right (f : PowerSeries K) :
    rightZeroMap (rename (fun _ : Unit => Sum.inr ()) f)=PowerSeries.C (PowerSeries.constantCoeff f) := by
  rw [rightZeroMap_apply,rename_eq_subst,
    subst_comp_subst_apply (HasSubst.X_comp _) hasSubst_rightZero]
  simp only [Function.comp_apply]
  have hh : (fun u : Unit => subst (rightZero (K:=K))
      (X (Sum.inr ()) : MvPowerSeries (Unit⊕Unit) K))=(0 : Unit → PowerSeries K) := by
    funext u
    rw [subst_X hasSubst_rightZero]
    rfl
  rw [hh]
  exact subst_zero_eq_C_constantCoeff

/-- The true slope specialization is obtained from its divided-difference
identity, with no invocation of an inverse of X in the series ring. -/
theorem X_mul_rightZero_slope (W : WeierstrassCurve K) :
    (PowerSeries.X:PowerSeries K)*rightZeroMap W.slopeSeries=W.wSeries := by
  have h := congrArg (rightZeroMap (K:=K)) W.slopeSeries_mul_sub
  rw [map_mul,map_sub,rightZeroMap_X_right,rightZeroMap_X_left,
    map_sub,rightZeroMap_rename_right,rightZeroMap_rename_left,W.constantCoeff_wSeries,map_zero] at h
  linear_combination -h

theorem rightZero_slope (W : WeierstrassCurve K) :
    rightZeroMap W.slopeSeries=(PowerSeries.X:PowerSeries K)^2*W.vSeries := by
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R:=K))
  rw [X_mul_rightZero_slope,W.wSeries_eq_X_pow_three_mul]
  ring

theorem rightZero_intercept (W : WeierstrassCurve K) : rightZeroMap W.interceptSeries=0 := by
  rw [W.interceptSeries_eq,map_sub,rightZeroMap_rename_right,map_mul,rightZeroMap_X_right,
    W.constantCoeff_wSeries,map_zero,mul_zero,sub_zero]

theorem rightZero_add (W : WeierstrassCurve K) : rightZeroMap W.addSeries=(PowerSeries.X:PowerSeries K) := by
  rw [rightZeroMap_apply]
  exact W.subst_unitR_addSeries

/-- Specializing the derivative of a right-variable series reads its true
linear coefficient. The derivative is the same replay_pderiv used by diffMatrix. -/
theorem rightZero_derivative_rename_right (f : PowerSeries K) :
    rightZeroMap (replay_pderiv (Sum.inr ()) (rename (fun _ : Unit => Sum.inr ()) f))=
      PowerSeries.C (PowerSeries.coeff 1 f) := by
  rw [rename_eq_subst,pderiv_subst (HasSubst.X_comp _)]
  simp only [Fintype.sum_unique,Function.comp_apply,replay_pderiv_X,ite_true,mul_one]
  rw [← rename_eq_subst,rightZeroMap_rename_right]
  congr 1
  change MvPowerSeries.coeff 0 (replay_pderiv () f)=PowerSeries.coeff 1 f
  rw [replay_coeff_pderiv]
  simp

/-- The actual intercept derivative at s=0 is minus the actual slope there. -/
theorem rightZero_derivative_intercept (W : WeierstrassCurve K) :
    rightZeroMap (replay_pderiv (Sum.inr ()) W.interceptSeries)= -rightZeroMap W.slopeSeries := by
  have hd := congrArg (replay_pderiv (Sum.inr ())) W.interceptSeries_eq
  rw [map_sub,pderiv_mul,replay_pderiv_X,if_pos rfl] at hd
  have h := congrArg (rightZeroMap (K:=K)) hd
  rw [map_sub,rightZero_derivative_rename_right,map_add,map_mul,map_mul,
    rightZeroMap_X_right,map_one,mul_zero,mul_one,add_zero,
    W.coeff_wSeries_of_lt (by decide:1<3),map_zero,zero_sub] at h
  exact h

/-- The specialized chord denominator is the SAME unit V of the actual curve. -/
theorem rightZero_shortChordDenom (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    rightZeroMap (shortChordDenom W)=W.vSeries := by
  unfold shortChordDenom
  rw [map_add,map_one,map_mul,rightZeroMap_C,map_pow,rightZero_slope]
  linear_combination -(short_v_equation W h1 h2 h3 h6)

#print axioms rightZero_slope
#print axioms rightZero_derivative_intercept
#print axioms rightZero_shortChordDenom
end FourCorner.CommonSource.LogPrecision
