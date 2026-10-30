import ThetaCoverClassPortable.ThetaQuadraticContactOrders

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaQuadraticContactDivisor
open ThetaQuadraticCurve ThetaQuadraticField ThetaQuadraticPlacePullback ThetaQuadraticHalfDivisor
open ThetaQuadraticBoundary ThetaQuadraticInfinityScheme ThetaQuadraticNativeDivisorIdentities
open ThetaQuadraticContactOrders ThetaQuadraticContactPlaces DivisorPicClassification
abbrev K := ThetaDGeometricModel.K
local instance : IsIntegral curve := curve_integral
local instance : Algebra F functionField := fieldAlgebra
local instance : IsCurveOver F functionField := field_isCurveOver
local instance : Algebra.EssFiniteType F functionField := field_essFiniteType
local instance : IsIntegral ThetaDGeometricModel.geometricD := ThetaDGeometricModel.geometric_integral
local instance : Algebra K ThetaDGeometricModel.field := ThetaDGeometricModel.fieldAlgebra
local instance : IsProper ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_proper
local instance : SmoothOfRelativeDimension 1 ThetaDGeometricModel.toBase := ThetaDGeometricModel.geometric_smooth

theorem geometric_infinity_coefficient (x : closedPoints ThetaDGeometricModel.geometricD) :
    ThetaDCanonicalInfinityDivisor.infinitySum (geometricPlace x)=H2 (sourcePlace x) := by
  have hh := ThetaQuadraticHalfUnweighted.actual_half_pullback_coefficient x
  have hn := congrArg (fun D : Divisor F functionField => D (sourcePlace x)) halfDivisor_eq
  have hp := congrArg (fun D : Divisor F functionField => D (sourcePlace x))
    ThetaQuadraticBoundaryHalfOrder.positive_half_is_E2
  simp only [Finsupp.sub_apply] at hh hn
  simp only [Finsupp.sup_apply,Finsupp.zero_apply] at hp
  have hH := ThetaCoverDivisor.infinitySum_effective (geometricPlace x)
  simp only [Finsupp.zero_apply] at hH
  by_cases he : ∃s : ThetaCoverBoundaryPoints.Signs,ThetaCoverBoundaryPoints.place s=geometricPlace x
  · obtain ⟨s,hs⟩ := he
    have hb := ThetaQuadraticBoundaryHalfOrder.geometric_boundary_half_one s
    rw [hs] at hb
    have hE : ThetaCoverBoundaryPoints.boundarySum (geometricPlace x)=1 := by
      rw [ThetaCoverBoundaryPoints.boundarySum_apply,if_pos ⟨s,hs⟩]
    simp only [Finsupp.sub_apply,hE] at hb hh
    rw [show halfDivisor (sourcePlace x)=1 by omega] at hp hn
    norm_num at hp
    omega
  · have hE : ThetaCoverBoundaryPoints.boundarySum (geometricPlace x)=0 := by
      rw [ThetaCoverBoundaryPoints.boundarySum_apply,if_neg he]
    rw [hE] at hh
    have hle : halfDivisor (sourcePlace x)≤0 := by omega
    rw [sup_eq_right.mpr hle] at hp
    omega

theorem H2_coefficient_range (w : Place F functionField) : H2 w=0 ∨ H2 w=1 := by
  rw [H2_apply]
  by_cases ht : place true=w
  · have hf : place false≠w := by
      intro hf; exact ThetaQuadraticInfinityDistinct.places_distinct (ht.trans hf.symm)
    simp [ht,hf]
  · by_cases hf : place false=w <;> simp [ht,hf]

theorem ell_all_place_bound (b : Bool) (w : Place F functionField) : -H2 w≤w.ord (ell b) := by
  obtain ⟨x,rfl⟩ := sourcePlace_surjective w
  have hs := scale_order x (ell b)
  have hp := scale_positive x
  have hg : 0≤(geometricPlace x).ord (toGeometric (ell b))+
      ThetaDCanonicalInfinityDivisor.infinitySum (geometricPlace x) := by
    cases b
    · have h := ThetaCoverContacts.minus_ord (geometricPlace x)
      have he := ThetaCoverContacts.minus_effective (geometricPlace x)
      simp only [ThetaQuadraticContactOrders.ell,Bool.false_eq_true,if_false,ellMinus2_image]
      simp only [Finsupp.zero_apply] at he
      omega
    · have h := ThetaCoverContacts.plus_ord (geometricPlace x)
      have he := ThetaCoverContacts.plus_effective (geometricPlace x)
      simp only [ThetaQuadraticContactOrders.ell,if_true,ellPlus2_image]
      simp only [Finsupp.zero_apply] at he
      omega
  rw [hs,geometric_infinity_coefficient] at hg
  rcases H2_coefficient_range (sourcePlace x) with h|h <;> rw [h] at hg ⊢ <;> nlinarith

/-- Exact native contact-line divisor obtained from actual DVR vanishing,
all-place pole bounds and the genuine weighted residue degrees. -/
theorem actual_divisor_ell (b : Bool) : principalDivisor (K:=F) (ell b) (ell_ne_zero b)=
    (2:ℕ) • contactDivisor b-H2 := by
  let T := principalDivisor (K:=F) (ell b) (ell_ne_zero b)+H2-(2:ℕ) • contactDivisor b
  have ht : 0≤T := by
    intro w
    simp only [T,Finsupp.sub_apply,Finsupp.add_apply,Finsupp.smul_apply,nsmul_eq_mul,
      Nat.cast_ofNat,principalDivisor_apply,contactDivisor,Finsupp.single_apply,Finsupp.zero_apply]
    by_cases hw : contactPlace b=w
    · rw [if_pos hw,←hw]
      have h := contact_line_order b
      have hH := H2_effective (contactPlace b)
      simp only [Finsupp.zero_apply] at hH
      omega
    · rw [if_neg hw,mul_zero,sub_zero]
      have h := ell_all_place_bound b w
      omega
  have hd : Divisor.degree T=0 := by
    simp only [T,map_sub,map_add,map_nsmul,degree_principalDivisor,H2_degree,
      contactDivisor_degree,nsmul_eq_mul,Nat.cast_ofNat]
    norm_num
  have hz := ThetaQuadraticDivisorPositivity.effective_degree_zero_eq_zero T ht hd
  apply Finsupp.ext
  intro w
  have h := congrArg (fun D : Divisor F functionField => D w) hz
  simp only [T,Finsupp.sub_apply,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.zero_apply,
    nsmul_eq_mul,Nat.cast_ofNat] at h ⊢
  omega

end FourCorner.ThetaQuadraticContactDivisor
