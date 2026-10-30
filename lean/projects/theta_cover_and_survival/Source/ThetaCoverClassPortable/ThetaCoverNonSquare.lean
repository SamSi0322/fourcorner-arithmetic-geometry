import ThetaCoverClassPortable.ThetaCoverClass

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaCoverNonSquare
open ThetaDGeometricModel ThetaCoverFunctions ThetaCoverDivisor ThetaCoverClass
open ThetaCoverBoundaryPoints ThetaDCanonicalInfinityDivisor DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

/-- The literal h is not a square in the ACTUAL geometric function field.
This is derived from the genuine nonzero divisor class, not assumed from
connected-cover labels or an abstract square-class avatar. -/
theorem literal_h_not_square : ¬∃f : field,f^2=h := by
  rintro ⟨f,hf⟩
  have hf0 : f≠0 := by
    intro hz
    rw [hz,zero_pow (by decide)] at hf
    exact h_ne_zero hf.symm
  have hp : (boundarySum-infinitySum).IsPrincipal := by
    refine ⟨f,hf0,fun w=>?_⟩
    have hh:=congrArg (fun D : Divisor K field=>D w) actual_divisor_h
    simp only [principalDivisor_apply,Finsupp.sub_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat] at hh
    have hs : w.ord h=w.ord f+w.ord f := by
      rw [←hf,pow_two,w.ord_mul hf0 hf0]
    simp only [Finsupp.sub_apply]
    omega
  apply geometric_class_nonzero
  exact (QuotientAddGroup.eq_zero_iff _).mpr hp

#print axioms literal_h_not_square
end FourCorner.ThetaCoverNonSquare
