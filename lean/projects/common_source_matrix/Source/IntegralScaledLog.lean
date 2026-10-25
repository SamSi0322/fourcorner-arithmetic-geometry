import FormalLogOdd
import Mathlib.NumberTheory.Padics.RingHoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman IsLocalRing

/-- The genuine characteristic-zero formal logarithm after the canonical
integral-to-field coefficient embedding. -/
def literalLog (Phi : FormalGroupLaw ℤ_[2] Unit) : PowerSeries ℚ_[2] :=
  (Phi.map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])).log ()

@[simp] theorem literalLog_coeff_zero (Phi : FormalGroupLaw ℤ_[2] Unit) :
    PowerSeries.coeff 0 (literalLog Phi)=0 := by
  change MvPowerSeries.coeff (Finsupp.single () 0) ((Phi.map PadicInt.Coe.ringHom).log ())=0
  simpa only [Finsupp.single_zero,MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using
    (Phi.map PadicInt.Coe.ringHom).constantCoeff_log ()

@[simp] theorem literalLog_coeff_one (Phi : FormalGroupLaw ℤ_[2] Unit) :
    PowerSeries.coeff 1 (literalLog Phi)=1 := by
  change MvPowerSeries.coeff (Finsupp.single () 1) ((Phi.map PadicInt.Coe.ringHom).log ())=1
  simpa using (Phi.map PadicInt.Coe.ringHom).coeff_single_log () ()

lemma two_mem_maximal : (2:ℤ_[2]) ∈ maximalIdeal ℤ_[2] := by
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (Set.mem_singleton 2)

/-- The divided scaled coefficients 2^(m-1)*lambda_m are genuinely integral.
The proof uses the denominator bound of the specified formal logarithm. -/
theorem divided_scaled_coefficient_integral (Phi : FormalGroupLaw ℤ_[2] Unit) (m : ℕ) :
    ∃ c : ℤ_[2], (c:ℚ_[2])=(2:ℚ_[2])^(m-1)*PowerSeries.coeff m (literalLog Phi) := by
  by_cases hm : m=0
  · subst m
    refine ⟨0,?_⟩
    rw [literalLog_coeff_zero]
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hle : padicValNat 2 m ≤ m-1 := by
      have hlt : padicValNat 2 m < m :=
        lt_of_lt_of_le (Nat.lt_pow_self (by decide:1<2)) (Nat.le_of_dvd hmpos pow_padicValNat_dvd)
      omega
    obtain ⟨c,hc⟩ := Phi.coeff_log_map_padic Nat.prime_two two_mem_maximal
      (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) (by change (2:ℚ_[2]) ≠ 0;norm_num) () (Finsupp.single () m)
    have hc' : (2:ℚ_[2])^(padicValNat 2 m)*PowerSeries.coeff m (literalLog Phi)=(c:ℚ_[2]) := by
      simp only [Finsupp.degree_single] at hc
      change (2:ℚ_[2])^(padicValNat 2 m)*PowerSeries.coeff m (literalLog Phi)=(c:ℚ_[2]) at hc
      exact hc
    refine ⟨(2:ℤ_[2])^(m-1-padicValNat 2 m)*c,?_⟩
    rw [PadicInt.coe_mul,PadicInt.coe_pow]
    have htwo : ((2:ℤ_[2]):ℚ_[2])=2 := rfl
    rw [htwo,← hc',← mul_assoc,← pow_add,Nat.sub_add_cancel hle]

/-- An integral series canonically tied to Lambda(2T)/2 coefficient by coefficient. -/
def dividedScaledLog (Phi : FormalGroupLaw ℤ_[2] Unit) : PowerSeries ℤ_[2] :=
  PowerSeries.mk (fun m => Classical.choose (divided_scaled_coefficient_integral Phi m))

theorem dividedScaledLog_coefficient (Phi : FormalGroupLaw ℤ_[2] Unit) (m : ℕ) :
    ((PowerSeries.coeff m (dividedScaledLog Phi):ℤ_[2]):ℚ_[2])=
      (2:ℚ_[2])^(m-1)*PowerSeries.coeff m (literalLog Phi) := by
  rw [dividedScaledLog,PowerSeries.coeff_mk]
  exact Classical.choose_spec (divided_scaled_coefficient_integral Phi m)

/-- Any integral series satisfying this exact coefficient relation is the same
series; Classical.choose introduces no mathematical normalization freedom. -/
theorem dividedScaledLog_unique (Phi : FormalGroupLaw ℤ_[2] Unit) (L : PowerSeries ℤ_[2])
    (hL : ∀ m, ((PowerSeries.coeff m L:ℤ_[2]):ℚ_[2])=
      (2:ℚ_[2])^(m-1)*PowerSeries.coeff m (literalLog Phi)) : L=dividedScaledLog Phi := by
  ext m
  apply PadicInt.ext
  exact (hL m).trans (dividedScaledLog_coefficient Phi m).symm

theorem dividedScaledLog_zero (Phi : FormalGroupLaw ℤ_[2] Unit) :
    PowerSeries.coeff 0 (dividedScaledLog Phi)=0 := by
  apply PadicInt.ext
  rw [dividedScaledLog_coefficient]
  rw [literalLog_coeff_zero]
  simp

theorem dividedScaledLog_one (Phi : FormalGroupLaw ℤ_[2] Unit) :
    PowerSeries.coeff 1 (dividedScaledLog Phi)=1 := by
  apply PadicInt.ext
  rw [dividedScaledLog_coefficient]
  rw [literalLog_coeff_one]
  simp

theorem formal_log_quadratic_of_inverse_neg {K : Type*} [Field K] [CharZero K]
    (Phi : FormalGroupLaw K Unit) (hinv : subst (negPair (R:=K)) (Phi.F ())=0) :
    coeff (Finsupp.single () 2) (Phi.log ())=0 := by
  have h := formal_log_odd Phi hinv
  have hr : subst (fun _ : Unit => -(X () : MvPowerSeries Unit K)) (Phi.log ())=
      rescale (fun _ : Unit => (-1:K)) (Phi.log ()) := by
    rw [rescale_eq_subst]
    congr 1
    funext u
    simp
  rw [hr] at h
  have hc := congrArg (coeff (Finsupp.single () 2)) h
  simp only [coeff_rescale,map_neg,Finsupp.prod_single_index,pow_zero,neg_one_sq,one_mul] at hc
  linear_combination (1/2:K)*hc

/-- The coefficient embedding preserves the literal short-curve inverse,
so its mapped formal logarithm has zero quadratic coefficient. -/
theorem integral_short_log_quadratic (W : WeierstrassCurve ℤ_[2])
    (h1 : W.a₁=0) (h3 : W.a₃=0) : PowerSeries.coeff 2 (literalLog W.formalGroupLaw)=0 := by
  apply formal_log_quadratic_of_inverse_neg
  change subst (negPair (R:=ℚ_[2])) (MvPowerSeries.map PadicInt.Coe.ringHom W.addSeries)=0
  rw [W.map_addSeries]
  apply short_inverse_substitution
  · simpa [WeierstrassCurve.map] using congrArg (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) h1
  · simpa [WeierstrassCurve.map] using congrArg (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2]) h3

theorem dividedScaledLog_quadratic (W : WeierstrassCurve ℤ_[2])
    (h1 : W.a₁=0) (h3 : W.a₃=0) : PowerSeries.coeff 2 (dividedScaledLog W.formalGroupLaw)=0 := by
  apply PadicInt.ext
  rw [dividedScaledLog_coefficient,integral_short_log_quadratic W h1 h3]
  simp

/-- A genuine integral cubic remainder for the divided scaled logarithm. -/
theorem dividedScaledLog_cubic (W : WeierstrassCurve ℤ_[2]) (h1 : W.a₁=0) (h3 : W.a₃=0) :
    ∃ D : PowerSeries ℤ_[2], dividedScaledLog W.formalGroupLaw=
      PowerSeries.X+PowerSeries.X^3*D := by
  have hd : (PowerSeries.X : PowerSeries ℤ_[2])^3 ∣ dividedScaledLog W.formalGroupLaw-PowerSeries.X := by
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro m hm
    interval_cases m
    · rw [map_sub,dividedScaledLog_zero,PowerSeries.coeff_X];norm_num
    · rw [map_sub,dividedScaledLog_one,PowerSeries.coeff_X];norm_num
    · rw [map_sub,dividedScaledLog_quadratic W h1 h3,PowerSeries.coeff_X];norm_num
  obtain ⟨D,hD⟩ := hd
  exact ⟨D,by linear_combination hD⟩

#print axioms divided_scaled_coefficient_integral
#print axioms dividedScaledLog_unique
#print axioms integral_short_log_quadratic
#print axioms dividedScaledLog_cubic
end FourCorner.CommonSource.LogPrecision
