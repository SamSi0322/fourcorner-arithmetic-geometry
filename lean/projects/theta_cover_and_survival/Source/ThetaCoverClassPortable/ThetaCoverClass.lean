import ThetaCoverClassPortable.ThetaCoverDivisor
import ThetaCoverClassPortable.ThetaCoverContacts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaCoverClass
open ThetaDGeometricModel ThetaCoverFunctions ThetaCoverBoundaryPoints ThetaCoverDivisor
open ThetaCoverContacts ThetaDCanonicalInfinityDivisor DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

theorem squareMultiplier_ne_zero : squareMultiplier≠0 :=
  div_ne_zero numerator_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) radical_ne_zero) ellPlus_ne_zero)

/-- Equality of ACTUAL divisors after cancelling two in their integer
coefficients; no illicit cancellation of two in a Picard group occurs. -/
theorem exact_half_divisor :
    boundarySum-infinitySum=Bplus-Bminus+principalDivisor squareMultiplier squareMultiplier_ne_zero := by
  ext w
  have hd:=congrArg (fun D : Divisor K field=>D w) actual_divisor_h
  simp only [principalDivisor_apply,Finsupp.sub_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] at hd
  have hp:=plus_ord w
  have hm:=minus_ord w
  have hi:=congrArg w.ord exact_cover_identity
  have hq : w.ord (squareMultiplier^2)=2*w.ord squareMultiplier := by
    rw [pow_two,w.ord_mul squareMultiplier_ne_zero squareMultiplier_ne_zero]
    ring
  rw [w.ord_mul (div_ne_zero ellPlus_ne_zero ellMinus_ne_zero)
      (pow_ne_zero 2 squareMultiplier_ne_zero),hq,div_eq_mul_inv,
    w.ord_mul ellPlus_ne_zero (inv_ne_zero ellMinus_ne_zero),w.ord_inv] at hi
  simp only [Finsupp.sub_apply,Finsupp.add_apply,principalDivisor_apply]
  omega

/-- The geometric class of E0-H equals the difference of the TWO ACTUAL
contact divisors on the original curve, using the exact scalar identity. -/
theorem geometric_class_eq_contacts : geometricClass=divisorClass (Bplus-Bminus) := by
  apply (class_eq_iff_principal_sub _ _).mpr
  refine ⟨squareMultiplier,squareMultiplier_ne_zero,fun w=>?_⟩
  change ((boundarySum-infinitySum)-(Bplus-Bminus)) w=w.ord squareMultiplier
  rw [exact_half_divisor]
  simp only [Finsupp.sub_apply,Finsupp.add_apply,principalDivisor_apply]
  ring

 theorem geometric_class_nonzero : geometricClass≠0 := by
  rw [geometric_class_eq_contacts]
  exact contact_class_difference_ne_zero

/-- All geometric divisor-class conclusions, without silently identifying
the divisor Picard quotient with a represented Jacobian's rational points. -/
theorem actual_geometric_cover_class :
    principalDivisor h h_ne_zero=2 • boundarySum-2 • infinitySum ∧
    picDegree geometricClass=0 ∧ (2:ℕ) • geometricClass=0 ∧ geometricClass≠0 ∧
    geometricClass=divisorClass (Bplus-Bminus) :=
  ⟨actual_divisor_h,degree_class_zero,class_two_torsion,geometric_class_nonzero,geometric_class_eq_contacts⟩

#print axioms geometric_class_eq_contacts
#print axioms actual_geometric_cover_class
end FourCorner.ThetaCoverClass
