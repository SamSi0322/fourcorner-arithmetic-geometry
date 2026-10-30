import ThetaCoverClassPortable.ThetaQuadraticContactDivisor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaQuadraticContactClassIdentity
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticHalfDivisor
open ThetaQuadraticContactPlaces ThetaQuadraticContactDivisor DivisorPicClassification
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := fieldAlgebra
local instance : IsCurveOver F functionField := field_isCurveOver
local instance : Algebra.EssFiniteType F functionField := field_essFiniteType

theorem squareMultiplier2_ne_zero : squareMultiplier2≠0 := by
  intro hz
  have h := exact_quadratic_identity
  rw [hz,zero_pow (by decide),mul_zero] at h
  exact h2_ne_zero h

/-- Two is cancelled only in integer Weil coefficients, never in Pic0. -/
theorem exact_half_divisor : halfDivisor=Bplus2-Bminus2+
    principalDivisor (K:=F) squareMultiplier2 squareMultiplier2_ne_zero := by
  apply Finsupp.ext
  intro w
  have hd := congrArg (fun D : Divisor F functionField => D w) doubled_halfDivisor
  have hp := congrArg (fun D : Divisor F functionField => D w) (actual_divisor_ell true)
  have hm := congrArg (fun D : Divisor F functionField => D w) (actual_divisor_ell false)
  simp only [Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,principalDivisor_apply] at hd
  simp only [ThetaQuadraticContactOrders.ell,if_true,Bool.false_eq_true,if_false,
    principalDivisor_apply,Finsupp.sub_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] at hp hm
  have hi := congrArg w.ord exact_quadratic_identity
  have hq : w.ord (squareMultiplier2^2)=2*w.ord squareMultiplier2 := by
    rw [pow_two,w.ord_mul squareMultiplier2_ne_zero squareMultiplier2_ne_zero]
    ring
  rw [w.ord_mul (div_ne_zero ellPlus2_ne_zero ellMinus2_ne_zero)
      (pow_ne_zero 2 squareMultiplier2_ne_zero),hq,div_eq_mul_inv,
    w.ord_mul ellPlus2_ne_zero (inv_ne_zero ellMinus2_ne_zero),w.ord_inv] at hi
  simp only [Bplus2,Bminus2,Finsupp.sub_apply,Finsupp.add_apply,principalDivisor_apply]
  omega

/-- Equality in native Pic0 of the actual F-function field. -/
theorem coverClass_eq_contactClass : coverClass=contactClass := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change (halfDivisor-(Bplus2-Bminus2)).IsPrincipal
  refine ⟨squareMultiplier2,squareMultiplier2_ne_zero,fun w=>?_⟩
  rw [exact_half_divisor]
  simp only [Finsupp.sub_apply,Finsupp.add_apply,principalDivisor_apply]
  ring

theorem delta2_eq_contactClass : ThetaQuadraticNativeClasses.delta2=contactClass := by
  rw [←ThetaQuadraticNativeDivisorIdentities.coverClass_eq_delta2]
  exact coverClass_eq_contactClass

theorem contactClass_ne_zero : contactClass≠0 := by
  rw [←coverClass_eq_contactClass]
  exact coverClass_ne_zero

theorem contactClass_two_torsion : (2:ℕ) • contactClass=0 := by
  rw [←coverClass_eq_contactClass]
  exact coverClass_two_torsion

end FourCorner.ThetaQuadraticContactClassIdentity
