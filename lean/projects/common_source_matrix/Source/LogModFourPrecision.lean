import FormalLogEvaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman IsLocalRing

/-- The actual integral cubic remainder, tied to the complete specified series. -/
def cubicRemainder (W : WeierstrassCurve ℤ_[2]) (h1 : W.a₁=0) (h3 : W.a₃=0) : PowerSeries ℤ_[2] :=
  Classical.choose (dividedScaledLog_cubic W h1 h3)

theorem cubicRemainder_spec (W : WeierstrassCurve ℤ_[2]) (h1 : W.a₁=0) (h3 : W.a₃=0) :
    dividedScaledLog W.formalGroupLaw=PowerSeries.X+PowerSeries.X^3*cubicRemainder W h1 h3 :=
  Classical.choose_spec (dividedScaledLog_cubic W h1 h3)

/-- The evaluation argument is genuinely topologically nilpotent at every
paper depth nu=k+1>=2, including A=0. -/
theorem scaled_argument_mem (k : ℕ) (hk : 1 ≤ k) (A : ℤ_[2]) :
    (2:ℤ_[2])^k*A ∈ maximalIdeal ℤ_[2] :=
  Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ two_mem_maximal k (by omega))

/-- Integral representative of the logarithm divided by 2^(k+1). Its field
value is certified below from the actual convergent logarithmic series. -/
def integralScaledLogValue (W : WeierstrassCurve ℤ_[2]) (h1 : W.a₁=0) (h3 : W.a₃=0)
    (k : ℕ) (A : ℤ_[2]) : ℤ_[2] :=
  A+2^(2*k)*A^3*MvPSeries.eval (fun _ : Unit => (2:ℤ_[2])^k*A) (cubicRemainder W h1 h3)

theorem integralScaledLogValue_evaluation (W : WeierstrassCurve ℤ_[2])
    (h1 : W.a₁=0) (h3 : W.a₃=0) (k : ℕ) (hk : 1 ≤ k) (A : ℤ_[2]) :
    (2:ℤ_[2])^k*integralScaledLogValue W h1 h3 k A=
      MvPSeries.eval (fun _ : Unit => (2:ℤ_[2])^k*A) (dividedScaledLog W.formalGroupLaw) := by
  have heval : HasEval (fun _ : Unit => (2:ℤ_[2])^k*A) :=
    MvPSeries.hasEval_of_mem (fun _ => scaled_argument_mem k hk A)
  rw [cubicRemainder_spec W h1 h3,MvPSeries.eval_add heval,MvPSeries.eval_mul heval,
    MvPSeries.eval_pow heval]
  have hX : MvPSeries.eval (fun _ : Unit => (2:ℤ_[2])^k*A) (PowerSeries.X : PowerSeries ℤ_[2])=
      (2:ℤ_[2])^k*A := MvPSeries.eval_X _ ()
  rw [hX]
  have hpow : (2:ℤ_[2])^(2*k)=((2:ℤ_[2])^k)^2 := by rw [Nat.mul_comm 2 k,pow_mul]
  unfold integralScaledLogValue
  rw [hpow]
  ring

/-- This representative equals the value of the genuine logarithm at
z=2^(k+1)A, divided by precisely the paper's 2^(k+1). -/
theorem integralScaledLogValue_field (W : WeierstrassCurve ℤ_[2])
    (h1 : W.a₁=0) (h3 : W.a₃=0) (k : ℕ) (hk : 1 ≤ k) (A : ℤ_[2]) :
    (integralScaledLogValue W h1 h3 k A : ℚ_[2])=
      evaluatedLog W.formalGroupLaw ((2:ℤ_[2])^k*A)/(2:ℚ_[2])^(k+1) := by
  have hi := integralScaledLogValue_evaluation W h1 h3 k hk A
  have hfield : (2:ℚ_[2])^k*(integralScaledLogValue W h1 h3 k A : ℚ_[2])=
      (MvPSeries.eval (fun _ : Unit => (2:ℤ_[2])^k*A) (dividedScaledLog W.formalGroupLaw):ℤ_[2]) := by
    have hc := congrArg (fun z : ℤ_[2] => (z:ℚ_[2])) hi
    rw [PadicInt.coe_mul,PadicInt.coe_pow] at hc
    have htwo : ((2:ℤ_[2]):ℚ_[2])=2 := rfl
    rw [htwo] at hc
    exact hc
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2:ℚ_[2]) ≠ 0))).mpr
  unfold evaluatedLog
  rw [pow_succ]
  linear_combination (2:ℚ_[2])*hfield

/-- Exact mod-four precision of the actual scaled logarithm, at every allowed
common depth. No finite-depth cutoff or nonzero-parameter premise is used. -/
theorem integralScaledLogValue_mod_four (W : WeierstrassCurve ℤ_[2])
    (h1 : W.a₁=0) (h3 : W.a₃=0) (k : ℕ) (hk : 1 ≤ k) (A : ℤ_[2]) :
    PadicInt.toZModPow 2 (integralScaledLogValue W h1 h3 k A)=PadicInt.toZModPow 2 A := by
  have hpow : (2:ZMod 4)^(2*k)=0 := by
    have hd : 2 ≤ 2*k := by omega
    rw [← Nat.sub_add_cancel hd,pow_add,show (2:ZMod 4)^2=0 by decide,mul_zero]
  unfold integralScaledLogValue
  simp only [map_add,map_mul,map_pow,map_ofNat,hpow,zero_mul,add_zero]

#print axioms integralScaledLogValue_evaluation
#print axioms integralScaledLogValue_field
#print axioms integralScaledLogValue_mod_four
#print axioms evaluatedLog_hasSum
end FourCorner.CommonSource.LogPrecision
