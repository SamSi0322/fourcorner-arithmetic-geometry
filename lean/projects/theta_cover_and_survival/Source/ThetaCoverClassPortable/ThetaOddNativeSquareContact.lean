import ThetaCoverClassPortable.ThetaHalfCanonicalSquareContact
import ThetaCoverClassPortable.ThetaOddGaloisActionHom

namespace FourCorner.ThetaOddNativeSquareContact
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaRootCanonicalSections ThetaHalfCanonicalSquareContact
open ThetaOddNativeLineEquiv ThetaNativeDualCanonicalLines ThetaOddThetaCanonicalLines
open ThetaActualHalfCanonicalContacts ThetaContactOddness ThetaActualLineDifferentials
open ThetaLinesDualLines ThetaGaloisSchemeField
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

 theorem coefficients_ne_zero (L : ThetaLine K) : ThetaRootCanonicalSections.coefficients L≠0 :=
  by
    cases L with
    | affine α β => intro h;have hh:=congrFun h 2;simpa [ThetaRootCanonicalSections.coefficients] using hh
    | vertical t => intro h;have hh:=congrFun h 0;simpa [ThetaRootCanonicalSections.coefficients] using hh
    | yzero => intro h;have hh:=congrFun h 1;simpa [ThetaRootCanonicalSections.coefficients] using hh

 theorem planeToField_eq (L : ThetaLine K) :
    planeToField (ThetaRootCanonicalSections.coefficients L)=differential L := rfl

 theorem dualOf_eq (L : ThetaLine K) :
    dualOf (ThetaRootCanonicalSections.coefficients L) (coefficients_ne_zero L)=dualLineEquiv L := by
  rw [dualLineEquiv_apply]
  cases L <;> rfl

 theorem normalized_odd_iff_square (L : ThetaLine K) :
    IsOddCanonicalLine (dualLineEquiv L) ↔ IsThetaSquareContact L := by
  constructor
  · rintro ⟨a,ha,B,hline,hB,hell,hcan⟩
    have he := canonical_divisor_eq_of_dual_eq (coefficients_ne_zero L) ha
      ((dualOf_eq L).trans hline)
    have hc : canonicalDivisorOf (ThetaRootCanonicalSections.nonzero L)=(2:ℕ) • B := by
      rw [←hcan,←he]
    exact half_canonical_square_contact L B hc
  · intro h
    cases L with
    | affine α β =>
      obtain ⟨data⟩ := affine_contact_data α β h
      refine ⟨ThetaRootCanonicalSections.coefficients (.affine α β),coefficients_ne_zero _,
        data.divisor,(dualOf_eq _).symm,data.effective,?_,?_⟩
      · rw [affine_contact_ell_one α β h data]
        decide
      · exact data.doubled_divisor
    | vertical t =>
      obtain ⟨data⟩ := vertical_contact_data t h
      refine ⟨ThetaRootCanonicalSections.coefficients (.vertical t),coefficients_ne_zero _,
        data.divisor,(dualOf_eq _).symm,data.effective,?_,?_⟩
      · rw [vertical_contact_ell_one t h data]
        decide
      · exact data.doubled_divisor
    | yzero => exact False.elim (theta_yzero_not_bitangent ((theta_no_hyperflex .yzero).mp h))

 theorem intrinsic_odd_iff_square (P : NativeDual) :
    IsOddCanonicalLine P ↔ dualSquareContact P := by
  obtain ⟨L,rfl⟩ := dualLineEquiv.surjective P
  simpa only [dualSquareContact,Equiv.symm_apply_apply] using normalized_odd_iff_square L

#print axioms normalized_odd_iff_square
#print axioms intrinsic_odd_iff_square
end
end FourCorner.ThetaOddNativeSquareContact
