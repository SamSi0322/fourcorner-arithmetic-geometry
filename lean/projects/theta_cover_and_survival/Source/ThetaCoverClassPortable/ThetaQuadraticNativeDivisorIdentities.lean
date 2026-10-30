import ThetaCoverClassPortable.ThetaQuadraticInfinityHalfOrder
import ThetaCoverClassPortable.ThetaQuadraticNativeClasses

noncomputable section
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1800000
open AlgebraicGeometry AlgebraicCurve

namespace FourCorner.ThetaQuadraticNativeDivisorIdentities
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticHalfDivisor
open ThetaQuadraticBoundary ThetaQuadraticInfinityScheme
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsCurveOver F functionField := field_isCurveOver
local instance : Algebra.EssFiniteType F functionField := field_essFiniteType

/-- Coefficients of the actual two degree-two infinity cycles. -/
theorem H2_apply (w : Place F functionField) :
    H2 w=(if place true=w then 1 else 0)+(if place false=w then 1 else 0) := by
  classical
  simp only [H2,ActualClosedPointNativePlace.cycle,Finsupp.add_apply,Finsupp.single_apply]
  rfl

/-- The known positive part and the actual valuations at the two
quadratic infinity points exhaust the negative part by weighted degree. -/
theorem halfDivisor_eq : halfDivisor=E2-H2 := by
  classical
  let N : Divisor F functionField := E2-halfDivisor
  have hN : 0≤N := by
    intro w
    have h := congrArg (fun D : Divisor F functionField => D w)
      ThetaQuadraticBoundaryHalfOrder.positive_half_is_E2
    simp only [Finsupp.sup_apply,Finsupp.zero_apply] at h
    change 0≤E2 w-halfDivisor w
    rw [←h]
    exact sub_nonneg.mpr le_sup_left
  have hH : H2≤N := by
    intro w
    rw [H2_apply]
    change _≤E2 w-halfDivisor w
    by_cases ht : place true=w
    · have hf : place false≠w := by
        intro hf
        exact ThetaQuadraticInfinityDistinct.places_distinct (ht.trans hf.symm)
      rw [if_pos ht,if_neg hf,←ht,ThetaQuadraticInfinityHalfOrder.half_infinity_neg_one]
      have he := E2_effective (place true)
      simp only [Finsupp.zero_apply] at he
      omega
    · by_cases hf : place false=w
      · rw [if_neg ht,if_pos hf,←hf,ThetaQuadraticInfinityHalfOrder.half_infinity_neg_one]
        have he := E2_effective (place false)
        simp only [Finsupp.zero_apply] at he
        omega
      · rw [if_neg ht,if_neg hf,zero_add]
        exact hN w
  have hd : Divisor.degree (N-H2)=0 := by
    simp only [N,map_sub,E2_degree,halfDivisor_degree,H2_degree]
    norm_num
  have heq : N=H2 := sub_eq_zero.mp
    (ThetaQuadraticDivisorPositivity.effective_degree_zero_eq_zero (N-H2) (sub_nonneg.mpr hH) hd)
  apply Finsupp.ext
  intro w
  have h := congrArg (fun D : Divisor F functionField => D w) heq
  simp only [N,Finsupp.sub_apply] at h ⊢
  omega

/-- Exact native principal Weil divisor in F(D_F), with every actual
place covered and genuine residue-field degrees retained. -/
theorem actual_divisor_h2 : DivisorPicClassification.principalDivisor (K:=F) h2 h2_ne_zero=
    (2:ℕ) • (E2-H2) := by
  rw [←halfDivisor_eq,doubled_halfDivisor]

theorem coverClass_eq_delta2 : coverClass=ThetaQuadraticNativeClasses.delta2 := by
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact halfDivisor_eq

theorem delta2_two_torsion : (2:ℕ) • ThetaQuadraticNativeClasses.delta2=0 := by
  rw [←coverClass_eq_delta2]
  exact coverClass_two_torsion

theorem delta2_ne_zero : ThetaQuadraticNativeClasses.delta2≠0 := by
  rw [←coverClass_eq_delta2]
  exact coverClass_ne_zero

end FourCorner.ThetaQuadraticNativeDivisorIdentities
