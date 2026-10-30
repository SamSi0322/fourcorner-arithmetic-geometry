import IntegralScaledLog

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman IsLocalRing

/-- Exact coefficient identity for Lambda(2T)=2*Lhat(T), including degree zero. -/
theorem dividedScaledLog_doubled_coefficient (Phi : FormalGroupLaw ℤ_[2] Unit) (m : ℕ) :
    (2:ℚ_[2])*((PowerSeries.coeff m (dividedScaledLog Phi):ℤ_[2]):ℚ_[2])=
      (2:ℚ_[2])^m*PowerSeries.coeff m (literalLog Phi) := by
  rw [dividedScaledLog_coefficient]
  by_cases hm : m=0
  · subst m
    rw [literalLog_coeff_zero]
    simp
  · have hm1 : m-1+1=m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)
    rw [← mul_assoc,← pow_succ',hm1]

/-- The complete formal rescaling identity; the integral series is tied to the
specified invariant-differential logarithm, not just to low coefficients. -/
theorem dividedScaledLog_rescaling (Phi : FormalGroupLaw ℤ_[2] Unit) :
    PowerSeries.C (2:ℚ_[2])*PowerSeries.map PadicInt.Coe.ringHom (dividedScaledLog Phi)=
      MvPowerSeries.rescale (fun _ : Unit => (2:ℚ_[2])) (literalLog Phi) := by
  ext m
  rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_map]
  change (2:ℚ_[2])*((PowerSeries.coeff m (dividedScaledLog Phi):ℤ_[2]):ℚ_[2])=
    MvPowerSeries.coeff (Finsupp.single () m) (MvPowerSeries.rescale (fun _ : Unit => (2:ℚ_[2])) (literalLog Phi))
  rw [MvPowerSeries.coeff_rescale]
  simpa only [Finsupp.prod_single_index,pow_zero,PowerSeries.coeff_coeToMvPowerSeries] using
    dividedScaledLog_doubled_coefficient Phi m

/-- Evaluation at z=2t through the canonically coefficient-identical integral
series. The following HasSum theorem certifies its actual convergent meaning. -/
def evaluatedLog (Phi : FormalGroupLaw ℤ_[2] Unit) (t : ℤ_[2]) : ℚ_[2] :=
  2*(MvPSeries.eval (fun _ : Unit => t) (dividedScaledLog Phi) : ℤ_[2])

theorem evaluatedLog_hasSum (Phi : FormalGroupLaw ℤ_[2] Unit) (t : ℤ_[2])
    (ht : t ∈ maximalIdeal ℤ_[2]) :
    HasSum (fun d : Unit →₀ ℕ =>
      MvPowerSeries.coeff d (literalLog Phi) * d.prod (fun _ m => (2*(t:ℚ_[2]))^m))
      (evaluatedLog Phi t) := by
  have heval : MvPowerSeries.HasEval (fun _ : Unit => t) := MvPSeries.hasEval_of_mem (fun _ => ht)
  have hs := MvPSeries.hasSum_eval heval (dividedScaledLog Phi)
  have hcont : Continuous (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) := by
    exact continuous_subtype_val
  have hm := hs.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]).toAddMonoidHom hcont
  have htwo := hm.mul_left (2:ℚ_[2])
  have hfun : (fun d : Unit →₀ ℕ => (2:ℚ_[2])*
      (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
        (MvPowerSeries.coeff d (dividedScaledLog Phi) * d.prod (fun _ m => t^m)))=
      (fun d : Unit →₀ ℕ => MvPowerSeries.coeff d (literalLog Phi) *
        d.prod (fun _ m => (2*(t:ℚ_[2]))^m)) := by
    funext d
    have hd : d=Finsupp.single () (d ()) := Finsupp.unique_single d
    rw [hd]
    simp only [Finsupp.prod_single_index,pow_zero,PowerSeries.coeff_coeToMvPowerSeries,map_mul,map_pow]
    change (2:ℚ_[2])*(((PowerSeries.coeff (d ()) (dividedScaledLog Phi):ℤ_[2]):ℚ_[2])*(t:ℚ_[2])^(d ()))=
      PowerSeries.coeff (d ()) (literalLog Phi)*(2*(t:ℚ_[2]))^(d ())
    rw [← mul_assoc,dividedScaledLog_doubled_coefficient,mul_pow]
    ring
  change HasSum (fun d : Unit →₀ ℕ => (2:ℚ_[2])*
    (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])
      (MvPowerSeries.coeff d (dividedScaledLog Phi) * d.prod (fun _ m => t^m)))
    (evaluatedLog Phi t) at htwo
  rw [hfun] at htwo
  exact htwo

#print axioms dividedScaledLog_rescaling
#print axioms evaluatedLog_hasSum
end FourCorner.CommonSource.LogPrecision
