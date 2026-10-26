import Cs15569DyadicDepth
import ActualLogParameter

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource WeierstrassCurve.Affine IsLocalRing
noncomputable section
local instance : (dyadicCurve 15569).IsElliptic := dyadicCurve_isElliptic n15569_ne_zero
local instance : DecidableEq DyadicField := Classical.decEq _

abbrev LocalLevelThree := filtration (dyadic_model_eq 15569) 2

def dyadicResidueEight : DyadicIntegers →+* ZMod 8 :=
  (show ℤ_[2] →+* ZMod 8 from PadicInt.toZModPow 3).comp dyadicIntegerEquiv15.symm.toRingHom

private theorem scaled_parameter_error_eight (Q R : LocalLevelThree) :
    (8 : DyadicIntegers) ∣
      Dyadic.scaledParameter (dyadic_model_eq 15569) dyadic_maximalIdeal15 (Q+R) -
        (Dyadic.scaledParameter (dyadic_model_eq 15569) dyadic_maximalIdeal15 Q+
          Dyadic.scaledParameter (dyadic_model_eq 15569) dyadic_maximalIdeal15 R) := by
  have he := Dyadic.parameter_add_error (dyadic_model_eq 15569) Q R
  rw [dyadic_maximalIdeal15,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at he
  obtain ⟨w,hw⟩ := he
  refine ⟨w,?_⟩
  have h8 : (8 : DyadicIntegers) ≠ 0 := by
    intro hz
    have hh := congrArg dyadicIntegerEquiv15.symm hz
    norm_num only [map_ofNat,map_zero] at hh
  apply mul_left_cancel₀ h8
  rw [Dyadic.parameter_eq_two_pow_mul (dyadic_model_eq 15569) dyadic_maximalIdeal15,
    Dyadic.parameter_eq_two_pow_mul (dyadic_model_eq 15569) dyadic_maximalIdeal15,
    Dyadic.parameter_eq_two_pow_mul (dyadic_model_eq 15569) dyadic_maximalIdeal15] at hw
  norm_num at hw
  linear_combination hw

/-- Additivity modulo8 is proved from the actual formal addition error at
E_3; no logarithm or character-additivity hypothesis is supplied. -/
def localCharacterEight : LocalLevelThree →+ ZMod 8 :=
  AddMonoidHom.mk' (fun Q => dyadicResidueEight
    (Dyadic.scaledParameter (dyadic_model_eq 15569) dyadic_maximalIdeal15 Q)) (fun Q R => by
      obtain ⟨w,hw⟩ := scaled_parameter_error_eight Q R
      have hh := congrArg dyadicResidueEight hw
      simp only [map_sub,map_add,map_mul,map_ofNat] at hh
      rw [show (8 : ZMod 8)=0 by decide,zero_mul] at hh
      exact sub_eq_zero.mp hh)

def levelCharacterEight : Hlevel 15569 n15569_ne_zero 2 →+ ZMod 8 :=
  localCharacterEight.comp (rationalFiltrationMap15 15569 n15569_ne_zero 2)

def toLevelThree : ActualH →+ Hlevel 15569 n15569_ne_zero 2 :=
  AddSubgroup.inclusion actual_H_depth_three

/-- The actual whole-H character z/8 modulo8. Every H point is retained. -/
def phiEight : ActualH →+ ZMod 8 := levelCharacterEight.comp toLevelThree

theorem phiEight_formula (Q : ActualH) :
    phiEight Q=PadicInt.toZModPow 3 (usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree Q)) := rfl

/-- Literal coordinate identification of the integral character input. -/
theorem phiEight_parameter {x y : ℚ} (Q : ActualH)
    (he : (congruentCurve 15569).toAffine.Nonsingular x y)
    (hQ : (Q:E)=.some x y he) :
    (usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree Q) : ℚ_[2])=
      (-(x : ℚ_[2])/y)/8 := by
  have hh := usualScaledParameter_coordinate 15569 n15569_ne_zero 2 (toLevelThree Q) x y he hQ
  rw [show (2 : ℚ_[2])^(2+1)=8 by norm_num] at hh
  exact hh

private theorem integral_fraction_residue (r : ℤ_[2]) (a b : ℤ)
    (hb : (b : ZMod 8) ≠ 0)
    (he : (r : ℚ_[2])=(a : ℚ_[2])/(b : ℚ_[2])) :
    PadicInt.toZModPow 3 r*(b : ZMod 8)=(a : ZMod 8) := by
  have hb0 : (b : ℚ_[2]) ≠ 0 := by
    intro hz
    have hbz : b=0 := by exact_mod_cast hz
    exact hb (by simp [hbz])
  have heq : r*(b : ℤ_[2])=(a : ℤ_[2]) := by
    apply PadicInt.ext
    push_cast
    rw [he,div_mul_cancel₀ _ hb0]
  have hr := congrArg (PadicInt.toZModPow 3) heq
  simpa only [map_mul,map_intCast] using hr

/-- The generator residues are attached to their actual rational points. -/
theorem phiEight_P : phiEight HP=6 := by
  rw [phiEight_formula]
  let r := usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree HP)
  have he : (r : ℚ_[2])=(7574730 : ℚ_[2])/(1199793847 : ℚ_[2]) := by
    rw [show (r : ℚ_[2])=(-(Cs15569Finite.px : ℚ_[2])/Cs15569Finite.py)/8 from
      phiEight_parameter HP _ rfl]
    norm_num [Cs15569Finite.px,Cs15569Finite.py]
  have hr := integral_fraction_residue r 7574730 1199793847 (by decide) he
  change PadicInt.toZModPow 3 r=6
  have hf : ∀ r : ZMod 8, r*1199793847=7574730 → r=6 := by decide
  exact hf _ hr

theorem phiEight_G : phiEight HG=7 := by
  rw [phiEight_formula]
  let r := usualScaledParameter 15569 n15569_ne_zero 2 (toLevelThree HG)
  have he : (r : ℚ_[2])=
      ((13522049*1672865 : ℤ) : ℚ_[2])/((1934751*2373852137 : ℤ) : ℚ_[2]) := by
    rw [show (r : ℚ_[2])=(-(Cs15569Finite.gx : ℚ_[2])/Cs15569Finite.gy)/8 from
      phiEight_parameter HG _ rfl]
    norm_num [Cs15569Finite.gx,Cs15569Finite.gy]
  have hr := integral_fraction_residue r (13522049*1672865) (1934751*2373852137) (by decide) he
  change PadicInt.toZModPow 3 r=7
  have hf : ∀ r : ZMod 8, r*(1934751*2373852137)=(13522049*1672865) → r=7 := by decide
  exact hf _ hr

/-- Exact SAME global mod8 coefficients evaluate in the actual character. -/
theorem phiEight_mod_eight {Q Z : ActualH} {k m : ℕ}
    (he : Q=k • HG+m • HP+8 • Z) : phiEight Q=7*k+6*m := by
  rw [he,map_add,map_add,map_nsmul,map_nsmul,map_nsmul,phiEight_G,phiEight_P]
  simp only [nsmul_eq_mul,Nat.cast_ofNat]
  rw [show (8 : ZMod 8)=0 by decide,zero_mul,add_zero]
  ring

#print axioms localCharacterEight
#print axioms phiEight
#print axioms phiEight_parameter
#print axioms phiEight_P
#print axioms phiEight_G
#print axioms phiEight_mod_eight
end
end FourCorner.Cs15569Completion
