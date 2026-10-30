import ShortLogIntegrand
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Module

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource.LogPrecision

variable {K F M : Type*} [Field K] [Field F] [Algebra K F]
  [AddCommGroup M] [Module F M] [Module K M] [IsScalarTower K F M]

/-- Every derivation of the actual algebraic unit relation has this derivative.
This applies in particular to the genuine universal Kaehler derivation. -/
theorem derivation_v_cleared (D : Derivation K F M) {a z V : F}
    (ha : D a=0) (hv : V=1+a*z^4*V^2) :
    (2-V) • D V=(4*a*z^3*V^3) • D z := by
  have hd := congrArg D hv
  simp only [map_add,D.map_one_eq_zero,D.leibniz,D.leibniz_pow,ha,zero_smul,add_zero,zero_add,
    Nat.reduceSub] at hd
  have hh : D V=(2*a*z^4*V) • D V+(4*a*z^3*V^2) • D z := by
    exact hd.trans (by module)
  have hc : ((1-2*a*z^4*V)*V) • D V=((4*a*z^3*V^2)*V) • D z := by
    calc
      ((1-2*a*z^4*V)*V) • D V=V • (D V-(2*a*z^4*V) • D V) := by module
      _=V • ((4*a*z^3*V^2) • D z) := by
        congr 1
        apply (sub_eq_iff_eq_add).mpr
        exact hh.trans (by module)
      _=((4*a*z^3*V^2)*V) • D z := by module
  have hvcoef : (1-2*a*z^4*V)*V=2-V := by linear_combination 2*hv
  rw [hvcoef] at hc
  have hcoef : (4*a*z^3*V^2)*V=4*a*z^3*V^3 := by ring
  rw [hcoef] at hc
  exact hc

theorem derivation_v_value (D : Derivation K F M) {a z V : F}
    (ha : D a=0) (hv : V=1+a*z^4*V^2) (hden : 2-V ≠ 0) :
    D V=(4*a*z^3*V^3/(2-V)) • D z := by
  have h := congrArg (fun m : M => (2-V)⁻¹ • m) (derivation_v_cleared D ha hv)
  rw [smul_smul,inv_mul_cancel₀ hden,one_smul,smul_smul] at h
  simpa only [div_eq_mul_inv,mul_comm] using h

/-- The literal curve-coordinate differential dx/(2y), with x=z/w, y=-1/w
and w=z^3 V. Its equality to V/(2-V) dz holds for every actual derivation,
not just a chosen formal differentiation rule. -/
theorem derivation_dx_over_two_y (D : Derivation K F M) {a z V : F}
    (ha : D a=0) (hv : V=1+a*z^4*V^2)
    (hz : z ≠ 0) (hV : V ≠ 0) (hden : 2-V ≠ 0) (h2 : (2:F) ≠ 0) :
    (2*(-1/(z^3*V)))⁻¹ • D (z/(z^3*V))=(V/(2-V)) • D z := by
  have hdV := derivation_v_value D ha hv hden
  have hdw : D (z^3*V)=
      (z^3*(4*a*z^3*V^3/(2-V))+3*z^2*V) • D z := by
    rw [D.leibniz,D.leibniz_pow,hdV]
    norm_num only [Nat.reduceSub]
    module
  rw [D.leibniz_div,hdw]
  simp only [smul_sub,smul_smul]
  rw [← sub_smul]
  congr 1
  have hw : z^3*V ≠ 0 := mul_ne_zero (pow_ne_zero 3 hz) hV
  have hs : (2*(-1/(z^3*V)))⁻¹*((z^3*V)⁻¹^2*(z^3*V))-
      (2*(-1/(z^3*V)))⁻¹*((z^3*V)⁻¹^2*
        (z*(z^3*(4*a*z^3*V^3/(2-V))+3*z^2*V)))=
      1+2*(a*z^4*V^2)/(2-V) := by
    field_simp [hz,hV,hden,h2]
    ring
  rw [hs]
  have hv' : a*z^4*V^2=V-1 := by linear_combination -hv
  rw [hv']
  field_simp [hden]
  ring

#print axioms derivation_v_cleared
#print axioms derivation_dx_over_two_y
end FourCorner.CommonSource.LogPrecision
