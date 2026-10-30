import LiteralFormalCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open ChabautyColeman
variable {K : Type*} [Field K]

/-- Normalized formal integration, defined directly by integrating coefficients. -/
def normalizedPrimitive (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk (fun m => PowerSeries.coeff (m-1) f/(m:K))

lemma normalizedPrimitive_zero (f : PowerSeries K) :
    PowerSeries.constantCoeff (normalizedPrimitive f)=0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,normalizedPrimitive,PowerSeries.coeff_mk]
  simp

theorem normalizedPrimitive_derivative [CharZero K] (f : PowerSeries K) :
    PowerSeries.derivative K (normalizedPrimitive f)=f := by
  apply PowerSeries.ext
  intro m
  rw [PowerSeries.coeff_derivative,normalizedPrimitive,PowerSeries.coeff_mk]
  have hm : ((m+1:ℕ):K) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ (PowerSeries.coeff m f) hm

theorem normalizedPrimitive_unique [CharZero K] (f g : PowerSeries K)
    (hd : PowerSeries.derivative K g=f) (hc : PowerSeries.constantCoeff g=0) :
    g=normalizedPrimitive f := by
  apply PowerSeries.derivative.ext
  · rw [hd,normalizedPrimitive_derivative]
  · rw [hc,normalizedPrimitive_zero]

/-- The paper's normalized formal integral of the actual pullback coefficient. -/
def paperEllSeries (W : WeierstrassCurve K) : PowerSeries K := normalizedPrimitive (shortOmega W)

lemma shortOmega_constant (W : WeierstrassCurve K) : PowerSeries.constantCoeff (shortOmega W)=1 := by
  have h := congrArg PowerSeries.constantCoeff (two_sub_v_mul_omega W)
  rw [map_mul,two_sub_v_constant,W.constantCoeff_vSeries,one_mul] at h
  exact h

/-- The homogeneous chart (z:-1:w) really specializes to the original point at
infinity. The unit V has constant1, so its differential coefficient is regular. -/
theorem formal_origin_and_normalization (W : WeierstrassCurve K) :
    (PowerSeries.constantCoeff (PowerSeries.X:PowerSeries K),
      PowerSeries.constantCoeff (-1:PowerSeries K),PowerSeries.constantCoeff W.wSeries)=(0,-1,0) ∧
    PowerSeries.constantCoeff W.vSeries=1 ∧ PowerSeries.constantCoeff (shortOmega W)=1 := by
  simp only [PowerSeries.constantCoeff_X,map_neg,map_one,W.constantCoeff_wSeries,
    W.constantCoeff_vSeries,shortOmega_constant,and_self]

/-- The normalized integral is identified with the SAME genuine formal group
logarithm by proved derivative and constant-term uniqueness. -/
theorem paperEllSeries_eq_canonical [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    paperEllSeries W=W.formalGroupLaw.log () := by
  symm
  apply normalizedPrimitive_unique
  · exact short_log_derivative W h1 h2 h3 h6
  · exact W.formalGroupLaw.constantCoeff_log ()

/-- Native geometric dx/(2y) pulls back to the coefficient whose normalized
formal antiderivative defines paperEllSeries. This is not the universal
algebraic differential of the transcendental logarithm itself. -/
theorem paperEllSeries_literal_pullback [CharZero K] (W : WeierstrassCurve K)
    (h1 : W.a₁=0) (h2 : W.a₂=0) (h3 : W.a₃=0) (h6 : W.a₆=0) :
    (2*formalY W)⁻¹ • (KaehlerDifferential.D K (FormalFrac K)) (formalX W)=
      formalMap (PowerSeries.derivative K (paperEllSeries W)) •
        (KaehlerDifferential.D K (FormalFrac K)) (formalZ:FormalFrac K) := by
  rw [paperEllSeries,normalizedPrimitive_derivative]
  exact literal_differential_pullback W h1 h2 h3 h6

/-- Original rational congruent curve, after the canonical dyadic embedding. -/
def paperDyadicCurve (n : ℤ) : WeierstrassCurve ℚ_[2] :=
  (congruentCurve (n:ℚ)).map (Rat.castHom ℚ_[2])

def paperLogSeries (n : ℤ) : PowerSeries ℚ_[2] := paperEllSeries (paperDyadicCurve n)

theorem paperDyadicCurve_short (n : ℤ) :
    (paperDyadicCurve n).a₁=0 ∧ (paperDyadicCurve n).a₂=0 ∧
      (paperDyadicCurve n).a₃=0 ∧ (paperDyadicCurve n).a₆=0 := by
  simp [paperDyadicCurve,congruentCurve,WeierstrassCurve.map]

theorem paperLogSeries_eq_literal (n : ℤ) :
    paperLogSeries n=literalLog (logIntegralCurve n).formalGroupLaw := by
  obtain ⟨h1,h2,h3,h6⟩ := paperDyadicCurve_short n
  rw [paperLogSeries,paperEllSeries_eq_canonical _ h1 h2 h3 h6]
  exact (literalLog_original_curve n).symm

/-- Evaluate the normalized integral of the literal curve form at the SAME
actual H point. Its equality to the convergent canonical log is proved below. -/
def paperLog (n : ℤ) (hn : n ≠ 0) (P : H n hn) : ℚ_[2] :=
  ∑' d : Unit →₀ ℕ, MvPowerSeries.coeff d (paperLogSeries n) *
    d.prod (fun _ m => (pointParameter (P:Point (n:ℚ)))^m)

theorem paperLog_eq_canonical (n : ℤ) (hn : n ≠ 0) (P : H n hn) :
    paperLog n hn P=canonicalLog n hn P := by
  unfold paperLog canonicalLog
  rw [paperLogSeries_eq_literal]

theorem paperLog_hasSum (n : ℤ) (hn : n ≠ 0) (P : H n hn) :
    HasSum (fun d : Unit →₀ ℕ => MvPowerSeries.coeff d (paperLogSeries n) *
      d.prod (fun _ m => (pointParameter (P:Point (n:ℚ)))^m)) (paperLog n hn P) := by
  rw [paperLogSeries_eq_literal,paperLog_eq_canonical]
  exact canonicalLog_hasSum n hn P

/-- The integral representative is now certified against the paper's actual
normalized dx/(2y) integral, at every chosen whole-H depth. -/
theorem wholeLogInteger_paper_value (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) (P : H n hn) :
    (wholeLogInteger n hn k hdeep P:ℚ_[2])=paperLog n hn P/(2:ℚ_[2])^(k+1) := by
  rw [paperLog_eq_canonical]
  exact wholeLogInteger_value n hn k hk hdeep P

def paperLogCharacter (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) : H n hn →+ ZMod 4 :=
  canonicalLogCharacter n hn k hk hdeep

theorem paperLogCharacter_eq_parameter (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) :
    paperLogCharacter n hn k hk hdeep=paperDyadicCharacter15 n hn k hk hdeep :=
  canonicalLogCharacter_eq_parameter n hn k hk hdeep

#print axioms paperEllSeries_eq_canonical
#print axioms paperEllSeries_literal_pullback
#print axioms formal_origin_and_normalization
#print axioms paperLog_hasSum
#print axioms wholeLogInteger_paper_value
#print axioms paperLogCharacter_eq_parameter
end FourCorner.CommonSource.LogPrecision
