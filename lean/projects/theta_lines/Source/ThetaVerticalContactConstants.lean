import ThetaAffineContactConstants

namespace FourCorner.ThetaVerticalContactConstants
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaGeometricContactPoints ThetaActualLineDifferentials
open ThetaContactDifferentialDivisors ThetaActualHalfCanonicalContacts
open ThetaCanonicalLinePointValues ThetaContactPairFrames ThetaContactLSpaceGeometry ThetaAffineContactConstants
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
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
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

 theorem vertical_contact_constants (t : K) (h : IsThetaSquareContact (.vertical t))
    (data : ContactData (verticalGlobalSection t)) :
    ∀g : field,g∈LSpace data.divisor → ∃c : K,algebraMap K field c=g := by
  obtain ⟨r,s,hr,hs,hrs,hpq,hdiv,hFr,hFs⟩ := vertical_pair_frames t h
  let P := verticalPlace t r hr
  let Q := verticalPlace t s hs
  let B : Divisor K field := Finsupp.single P 1+Finsupp.single Q 1
  have hPQ : P≠Q := hpq
  have hcan : canonicalDivisorOf (verticalDifferential_ne_zero t)=(2:ℕ) • B :=
    hdiv.trans (double_points P Q).symm
  have hdata : (2:ℕ) • data.divisor=canonicalDivisorOf (verticalDifferential_ne_zero t) := data.half_canonical
  have hDB : data.divisor=B := double_divisor_injective _ _ (hdata.trans hcan)
  have hB : 0≤B := by rw [←hDB];exact data.effective
  have hP : B P=1 := by simp [B,hPQ,hPQ.symm]
  have hQ : B Q=1 := by simp [B,hPQ,hPQ.symm]
  intro g hg
  rw [hDB] at hg
  by_cases hg0 : g=0
  · exact ⟨0,by rw [map_zero,hg0]⟩
  · have hreg := lSpace_smul_regular B hB (verticalDifferential_ne_zero t) hcan g hg
    obtain ⟨a,ha⟩ := regular_is_line hreg
    have hη : lineDifferential a≠0 := by rw [ha];exact smul_ne_zero hg0 (verticalDifferential_ne_zero t)
    have hposP : 0<P.ordDifferential (lineDifferential a) := by
      rw [ha]
      have hh := lSpace_smul_order_bound B (verticalDifferential_ne_zero t) hcan g hg hg0 P
      rw [hP] at hh
      omega
    have hposQ : 0<Q.ordDifferential (lineDifferential a) := by
      rw [ha]
      have hh := lSpace_smul_order_bound B (verticalDifferential_ne_zero t) hcan g hg hg0 Q
      rw [hQ] at hh
      omega
    have hvR := vertical_relations t r hr
    have hvS := vertical_relations t s hs
    have heR : a 0*(t*r)+a 1*r+a 2=0 :=
      (Z_positive_iff_value_zero ![t*r,r] hvR a hη hFr).mp hposP
    have heS : a 0*(t*s)+a 1*s+a 2=0 :=
      (Z_positive_iff_value_zero ![t*s,s] hvS a hη hFs).mp hposQ
    obtain ⟨h1,h2⟩ := vertical_two_point_coefficients t r s hrs a heR heS
    have he : g • verticalDifferential t=algebraMap K field (a 0) • verticalDifferential t :=
      ha.symm.trans (vertical_line_scalar t a h1 h2)
    exact ⟨a 0,scalar_of_differential_equality (verticalDifferential_ne_zero t) g (a 0) he⟩

#print axioms vertical_contact_constants
end
end FourCorner.ThetaVerticalContactConstants
