import LogModFourPrecision
import ActualCharacterSign

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision
open ChabautyColeman

/-- The paper's literal integral model, now over the standard dyadic integers. -/
def logIntegralCurve (n : ℤ) : WeierstrassCurve ℤ_[2] := ⟨0,0,0,-(n:ℤ_[2])^2,0⟩

/-- Its coefficient embedding is the SAME rational congruent curve in Q_2. -/
theorem logIntegralCurve_field (n : ℤ) :
    (logIntegralCurve n).map (PadicInt.Coe.ringHom : ℤ_[2] →+* ℚ_[2])=
      (congruentCurve (n:ℚ)).map (Rat.castHom ℚ_[2]) := by
  ext <;> simp [logIntegralCurve,congruentCurve,WeierstrassCurve.map]

/-- The actual formal coordinate: zero at O and -x/y at finite points. -/
def pointParameter {n : ℚ} : Point n → ℚ_[2]
  | .zero => 0
  | .some x y _ => -(x:ℚ_[2])/y

theorem usualScaledParameter_zero (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    usualScaledParameter n hn k (0:Hlevel n hn k)=0 := by
  classical
  have hzero : rationalScaledParameter15 n hn k (0:Hlevel n hn k)=0 := by
    apply Subtype.ext
    letI := dyadicCurve_isElliptic hn
    change (Dyadic.scaledParameter (dyadic_model_eq n) dyadic_maximalIdeal15
      (rationalFiltrationMap15 n hn k (0:Hlevel n hn k)):DyadicField)=0
    rw [Dyadic.scaledParameter_coe_eq,map_zero,Dyadic.parameter_zero]
    change (0:DyadicField)/(2:DyadicField)^(k+1)=0
    exact zero_div _
  unfold usualScaledParameter
  rw [hzero,map_zero]

/-- Every actual point in the filtration has the same formal parameter after
undoing scaling; infinity is included explicitly. -/
theorem usualScaledParameter_parameter (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (P : Hlevel n hn k) :
    (2:ℚ_[2])^(k+1)*(usualScaledParameter n hn k P:ℚ_[2])=
      pointParameter (P:Point (n:ℚ)) := by
  rcases P with ⟨P,hP⟩
  cases P with
  | zero =>
    change (2:ℚ_[2])^(k+1)*(usualScaledParameter n hn k (0:Hlevel n hn k):ℚ_[2])=0
    rw [usualScaledParameter_zero]
    simp
  | some x y he =>
    rw [usualScaledParameter_coordinate n hn k ⟨.some x y he,hP⟩ x y he rfl]
    change (2:ℚ_[2])^(k+1)*((-(x:ℚ_[2])/y)/(2:ℚ_[2])^(k+1))= -(x:ℚ_[2])/y
    simpa only [mul_comm] using div_mul_cancel₀ (-(x:ℚ_[2])/y)
      (pow_ne_zero (k+1) (by norm_num : (2:ℚ_[2]) ≠ 0))

/-- The complete H inclusion retains this SAME point parameter at any chosen
common level, without a coordinate or finite-point exception. -/
theorem whole_H_parameter (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (hdeep : H n hn ≤ Hlevel n hn k) (P : H n hn) :
    (2:ℚ_[2])^(k+1)*(usualScaledParameter n hn k (paperHToLevel15 n hn k hdeep P):ℚ_[2])=
      pointParameter (P:Point (n:ℚ)) :=
  usualScaledParameter_parameter n hn k _

#print axioms logIntegralCurve_field
#print axioms usualScaledParameter_zero
#print axioms usualScaledParameter_parameter
#print axioms whole_H_parameter
end FourCorner.CommonSource.LogPrecision
