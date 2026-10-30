import ActualLogParameter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open MvPowerSeries ChabautyColeman

/-- The actual canonical formal-logarithm series evaluated at the SAME
rational H point's parameter. Convergence is proved below, including O. -/
def canonicalLog (n : ℤ) (hn : n ≠ 0) (P : H n hn) : ℚ_[2] :=
  ∑' d : Unit →₀ ℕ, MvPowerSeries.coeff d (literalLog (logIntegralCurve n).formalGroupLaw) *
    d.prod (fun _ m => (pointParameter (P:Point (n:ℚ)))^m)

/-- An actual integral representative of the scaled canonical logarithm. -/
def wholeLogInteger (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (hdeep : H n hn ≤ Hlevel n hn k) (P : H n hn) : ℤ_[2] :=
  integralScaledLogValue (logIntegralCurve n) rfl rfl k
    (usualScaledParameter n hn k (paperHToLevel15 n hn k hdeep P))

/-- The convergent sum is the actual logarithmic series at the original point,
not a new local point obtained by choosing a compatible residue. -/
theorem wholeLogInteger_hasSum (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) (P : H n hn) :
    HasSum (fun d : Unit →₀ ℕ =>
      MvPowerSeries.coeff d (literalLog (logIntegralCurve n).formalGroupLaw) *
        d.prod (fun _ m => (pointParameter (P:Point (n:ℚ)))^m))
      ((2:ℚ_[2])^(k+1)*(wholeLogInteger n hn k hdeep P:ℚ_[2])) := by
  let A := usualScaledParameter n hn k (paperHToLevel15 n hn k hdeep P)
  let t : ℤ_[2] := 2^k*A
  have hs := evaluatedLog_hasSum (logIntegralCurve n).formalGroupLaw t (scaled_argument_mem k hk A)
  have hz : 2*(t:ℚ_[2])=pointParameter (P:Point (n:ℚ)) := by
    calc
      2*(t:ℚ_[2])=(2:ℚ_[2])^(k+1)*(A:ℚ_[2]) := by
        dsimp [t]
        change (2:ℚ_[2])*((2:ℚ_[2])^k*(A:ℚ_[2]))=(2:ℚ_[2])^(k+1)*(A:ℚ_[2])
        rw [pow_succ]
        ring
      _ = _ := whole_H_parameter n hn k hdeep P
  have hi := integralScaledLogValue_field (logIntegralCurve n) rfl rfl k hk A
  have he : evaluatedLog (logIntegralCurve n).formalGroupLaw t=
      (2:ℚ_[2])^(k+1)*(wholeLogInteger n hn k hdeep P:ℚ_[2]) := by
    have hmul := (eq_div_iff (pow_ne_zero (k+1) (by norm_num : (2:ℚ_[2]) ≠ 0))).mp hi
    simpa only [mul_comm,wholeLogInteger,t,A] using hmul.symm
  rw [hz,he] at hs
  exact hs

/-- The series defines a genuine sum on every point of the actual subgroup H. -/
theorem canonicalLog_hasSum (n : ℤ) (hn : n ≠ 0) (P : H n hn) :
    HasSum (fun d : Unit →₀ ℕ =>
      MvPowerSeries.coeff d (literalLog (logIntegralCurve n).formalGroupLaw) *
        d.prod (fun _ m => (pointParameter (P:Point (n:ℚ)))^m)) (canonicalLog n hn P) := by
  have hs := wholeLogInteger_hasSum n hn 1 (by decide) (le_refl _) P
  exact hs.summable.hasSum

/-- Every chosen common depth represents the SAME intrinsic logarithm divided
by precisely 2^(k+1); the logarithm itself is independent of that depth. -/
theorem wholeLogInteger_value (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) (P : H n hn) :
    (wholeLogInteger n hn k hdeep P:ℚ_[2])=canonicalLog n hn P/(2:ℚ_[2])^(k+1) := by
  have hs := (wholeLogInteger_hasSum n hn k hk hdeep P).tsum_eq
  change canonicalLog n hn P=(2:ℚ_[2])^(k+1)*(wholeLogInteger n hn k hdeep P:ℚ_[2]) at hs
  apply (eq_div_iff (pow_ne_zero (k+1) (by norm_num : (2:ℚ_[2]) ≠ 0))).mpr
  simpa only [mul_comm] using hs.symm

theorem wholeLogInteger_mod_four (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) (P : H n hn) :
    PadicInt.toZModPow 2 (wholeLogInteger n hn k hdeep P)=paperDyadicCharacter15 n hn k hk hdeep P := by
  have h := integralScaledLogValue_mod_four (logIntegralCurve n) rfl rfl k hk
    (usualScaledParameter n hn k (paperHToLevel15 n hn k hdeep P))
  exact h.trans (usualScaledParameter_residue n hn k hk (paperHToLevel15 n hn k hdeep P)).symm

/-- Genuine canonical-log character on the whole H, with additivity proved via
its exact mod-four identification with the actual parameter character. -/
def canonicalLogCharacter (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) : H n hn →+ ZMod 4 where
  toFun P := PadicInt.toZModPow 2 (wholeLogInteger n hn k hdeep P)
  map_zero' := by rw [wholeLogInteger_mod_four n hn k hk hdeep];exact map_zero _
  map_add' P Q := by
    rw [wholeLogInteger_mod_four n hn k hk hdeep,wholeLogInteger_mod_four n hn k hk hdeep,
      wholeLogInteger_mod_four n hn k hk hdeep]
    exact map_add _ _ _

theorem canonicalLogCharacter_eq_parameter (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) :
    canonicalLogCharacter n hn k hk hdeep=paperDyadicCharacter15 n hn k hk hdeep := by
  ext P
  exact wholeLogInteger_mod_four n hn k hk hdeep P

#print axioms wholeLogInteger_hasSum
#print axioms canonicalLog_hasSum
#print axioms wholeLogInteger_value
#print axioms canonicalLogCharacter
#print axioms canonicalLogCharacter_eq_parameter
end FourCorner.CommonSource.LogPrecision
