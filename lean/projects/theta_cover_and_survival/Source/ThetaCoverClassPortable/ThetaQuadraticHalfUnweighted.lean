import ThetaCoverClassPortable.ThetaQuadraticHalfDivisor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve

namespace FourCorner.ThetaQuadraticHalfUnweighted
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticPlacePullback ThetaQuadraticHalfDivisor
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : Algebra ThetaDGeometricModel.K ThetaDGeometricModel.field := ThetaDGeometricModel.fieldAlgebra
local instance : IsProper ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_proper
local instance : SmoothOfRelativeDimension 1 ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_smooth

theorem geometric_coefficient_range (x : closedPoints ThetaDGeometricModel.geometricD) :
    (ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum) (geometricPlace x)=1 ∨
    (ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum) (geometricPlace x)=0 ∨
    (ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum) (geometricPlace x)= -1 := by
  classical
  simp only [Finsupp.sub_apply,ThetaCoverBoundaryPoints.boundarySum_apply,
    ThetaDCanonicalInfinityDivisor.infinitySum_apply]
  split_ifs <;> norm_num

/-- The actual order factor is ONE wherever this particular divisor is
nonzero. This follows from integral coefficients and the independently
proved geometric coefficients ±1, rather than a ramification assumption. -/
theorem scale_one_or_half_zero (x : closedPoints ThetaDGeometricModel.geometricD) :
    scale x=1 ∨ halfDivisor (sourcePlace x)=0 := by
  have hc := geometric_half_coefficient x
  have hp := scale_positive x
  rcases geometric_coefficient_range x with h|h|h
  · rw [h] at hc
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hc.symm with h1|h1
    · exact Or.inl h1
    · omega
  · rw [h] at hc
    rcases mul_eq_zero.mp hc.symm with h1|h1
    · omega
    · exact Or.inr h1
  · rw [h] at hc
    have hm : scale x*(-halfDivisor (sourcePlace x))=1 := by
      rw [mul_neg,←hc]
      norm_num
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hm with h1|h1
    · exact Or.inl h1
    · omega

/-- Actual constant-field Weil pullback coefficients of the native F
half-divisor agree with the already constructed geometric E-H divisor. -/
theorem actual_half_pullback_coefficient (x : closedPoints ThetaDGeometricModel.geometricD) :
    (ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum) (geometricPlace x)=
      halfDivisor (sourcePlace x) := by
  have hc := geometric_half_coefficient x
  rcases scale_one_or_half_zero x with hs|hs
  · simpa only [hs,one_mul] using hc
  · rw [hs,mul_zero] at hc
    exact hc.trans hs.symm

/-- Every native F-place is accounted for by the actual closed-point
surjectivity, so this is not a statement about selected geometric labels. -/
theorem half_coefficient_range (w : Place F functionField) :
    halfDivisor w=1 ∨ halfDivisor w=0 ∨ halfDivisor w= -1 := by
  obtain ⟨x,rfl⟩ := sourcePlace_surjective w
  rw [←actual_half_pullback_coefficient x]
  exact geometric_coefficient_range x

end FourCorner.ThetaQuadraticHalfUnweighted
