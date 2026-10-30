import ThetaCoverClassPortable.ThetaQuadraticUnitCover

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve

namespace FourCorner.ThetaQuadraticHalfDivisor
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticPlacePullback DivisorPicClassification
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra
local instance : IsCurveOver F functionField := field_isCurveOver
local instance : Algebra.EssFiniteType F functionField := field_essFiniteType
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : Algebra ThetaDGeometricModel.K ThetaDGeometricModel.field := ThetaDGeometricModel.fieldAlgebra
local instance : IsProper ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_proper
local instance : SmoothOfRelativeDimension 1 ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_smooth
local instance : IsCurveOver ThetaDGeometricModel.K ThetaDGeometricModel.field := ThetaDGeometricModel.field_isCurveOver
local instance : Algebra.EssFiniteType ThetaDGeometricModel.K ThetaDGeometricModel.field := ThetaDGeometricModel.field_essFiniteType

/-- The actual finite-support native divisor div(h2)/2. Its integral
coefficients are justified by the proved actual unit-root cover. -/
def halfDivisor : Divisor F functionField :=
  (principalDivisor h2 h2_ne_zero).mapRange (fun n : ℤ => n/2) (by decide)

theorem doubled_halfDivisor : (2:ℕ) • halfDivisor=principalDivisor h2 h2_ne_zero := by
  apply Finsupp.ext
  intro w
  simp only [halfDivisor,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,
    Finsupp.mapRange_apply,principalDivisor_apply]
  obtain ⟨n,hn⟩ := ThetaQuadraticUnitCover.h2_order_even w
  rw [hn]
  omega

theorem halfDivisor_degree : Divisor.degree halfDivisor=0 := by
  have h := congrArg Divisor.degree doubled_halfDivisor
  rw [map_nsmul,degree_principalDivisor] at h
  simp only [nsmul_eq_mul,Nat.cast_ofNat] at h
  omega

def zeroDegreeHalf : Divisor.degZero (K:=F) (F:=functionField) :=
  ⟨halfDivisor,Divisor.mem_degZero.mpr halfDivisor_degree⟩
def coverClass : Pic0 F functionField := Pic0.mk zeroDegreeHalf

theorem coverClass_two_torsion : (2:ℕ) • coverClass=0 := by
  change QuotientAddGroup.mk ((2:ℕ) • zeroDegreeHalf)=0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change ((2:ℕ) • halfDivisor).IsPrincipal
  rw [doubled_halfDivisor]
  exact ⟨h2,h2_ne_zero,by intro w;rw [principalDivisor_apply]⟩

def scale (x : closedPoints ThetaDGeometricModel.geometricD) : ℤ :=
  Classical.choose (actual_order_scale x)
theorem scale_positive (x : closedPoints ThetaDGeometricModel.geometricD) : 0<scale x :=
  (Classical.choose_spec (actual_order_scale x)).1
theorem scale_order (x : closedPoints ThetaDGeometricModel.geometricD) (f : functionField) :
    (geometricPlace x).ord (toGeometric f)=scale x*(sourcePlace x).ord f :=
  (Classical.choose_spec (actual_order_scale x)).2 f

/-- A genuine native Weil coefficient comparison across F -> Qbar,
using the actual local DVR map and its actual positive order factor. -/
theorem geometric_half_coefficient (x : closedPoints ThetaDGeometricModel.geometricD) :
    (ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum) (geometricPlace x)=
      scale x*halfDivisor (sourcePlace x) := by
  have hg := congrArg (fun D : Divisor ThetaDGeometricModel.K ThetaDGeometricModel.field =>
    D (geometricPlace x)) ThetaCoverDivisor.actual_divisor_h
  simp only [Finsupp.sub_apply,Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,
    principalDivisor_apply] at hg
  have hs := scale_order x h2
  rw [h2_image] at hs
  have hd := congrArg (fun D : Divisor F functionField => D (sourcePlace x)) doubled_halfDivisor
  simp only [Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,principalDivisor_apply] at hd
  have hmul : scale x*(sourcePlace x).ord h2=2*(scale x*halfDivisor (sourcePlace x)) := by
    rw [←hd]
    ring
  rw [hmul] at hs
  simp only [Finsupp.sub_apply]
  omega

/-- Principality of the actual F half-divisor would give an ACTUAL
geometric principal function, by the proved all-point coefficient law. -/
theorem half_not_principal : ¬halfDivisor.IsPrincipal := by
  rintro ⟨f,hf,hord⟩
  apply ThetaCoverClass.geometric_class_nonzero
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change (ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum).IsPrincipal
  refine ⟨toGeometric f,?_,?_⟩
  · simpa only [map_zero] using toGeometric.injective.ne hf
  · intro w
    obtain ⟨x,rfl⟩ := SmoothProperClosedPointPlaces.placeOfClosedPoint_surjective ThetaDGeometricModel.toBase w
    rw [geometric_half_coefficient,hord]
    exact (scale_order x f).symm

theorem coverClass_ne_zero : coverClass≠0 := by
  intro h
  have hp := (QuotientAddGroup.eq_zero_iff zeroDegreeHalf).mp h
  exact half_not_principal hp

end FourCorner.ThetaQuadraticHalfDivisor
