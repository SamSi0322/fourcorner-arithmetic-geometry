import ThetaCoverClassPortable.ThetaContactLSpaceGeometry

namespace FourCorner.ThetaAffineContactConstants
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaGeometricContactPoints ThetaActualLineDifferentials
open ThetaContactDifferentialDivisors ThetaActualHalfCanonicalContacts
open ThetaCanonicalLinePointValues ThetaContactPairFrames ThetaContactLSpaceGeometry
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

/-- Half-divisors here are actual integral Weil divisors, so doubling is
injective. This makes the geometry independent of choices/order of roots. -/
theorem double_divisor_injective (B C : Divisor K field) (h : (2:ℕ) • B=(2:ℕ) • C) : B=C := by
  ext w
  have hh := congrArg (fun D : Divisor K field=>D w) h
  simp only [two_smul,Finsupp.add_apply] at hh
  omega

/-- Every L(B) element for the actual affine-line contact divisor is a TRUE
base-field constant. This includes g=0 and every actual place at infinity.
No ell1/oddness/nonhyperellipticity assumption is introduced. -/
theorem affine_contact_constants (α β : K) (h : IsThetaSquareContact (.affine α β))
    (data : ContactData (affineGlobalSection α β)) :
    ∀g : field,g∈LSpace data.divisor → ∃c : K,algebraMap K field c=g := by
  obtain ⟨r,s,hr,hs,hrs,hpq,hdiv,hFr,hFs⟩ := affine_pair_frames α β h
  let P := affinePlace α β r hr
  let Q := affinePlace α β s hs
  let B : Divisor K field := Finsupp.single P 1+Finsupp.single Q 1
  have hPQ : P≠Q := hpq
  have hcan : canonicalDivisorOf (affineDifferential_ne_zero α β)=(2:ℕ) • B :=
    hdiv.trans (double_points P Q).symm
  have hdata : (2:ℕ) • data.divisor=canonicalDivisorOf (affineDifferential_ne_zero α β) := data.half_canonical
  have hDB : data.divisor=B := double_divisor_injective _ _ (hdata.trans hcan)
  have hB : 0≤B := by rw [←hDB];exact data.effective
  have hP : B P=1 := by simp [B,hPQ,hPQ.symm]
  have hQ : B Q=1 := by simp [B,hPQ,hPQ.symm]
  intro g hg
  rw [hDB] at hg
  by_cases hg0 : g=0
  · exact ⟨0,by rw [map_zero,hg0]⟩
  · have hreg := lSpace_smul_regular B hB (affineDifferential_ne_zero α β) hcan g hg
    obtain ⟨a,ha⟩ := regular_is_line hreg
    have hη : lineDifferential a≠0 := by rw [ha];exact smul_ne_zero hg0 (affineDifferential_ne_zero α β)
    have hposP : 0<P.ordDifferential (lineDifferential a) := by
      rw [ha]
      have hh := lSpace_smul_order_bound B (affineDifferential_ne_zero α β) hcan g hg hg0 P
      rw [hP] at hh
      omega
    have hposQ : 0<Q.ordDifferential (lineDifferential a) := by
      rw [ha]
      have hh := lSpace_smul_order_bound B (affineDifferential_ne_zero α β) hcan g hg hg0 Q
      rw [hQ] at hh
      omega
    have hvR := affine_relations α β r hr
    have hvS := affine_relations α β s hs
    have heR : a 0*r+a 1+a 2*(α*r+β)=0 :=
      (Y_positive_iff_value_zero ![r,α*r+β] hvR a hη hFr).mp hposP
    have heS : a 0*s+a 1+a 2*(α*s+β)=0 :=
      (Y_positive_iff_value_zero ![s,α*s+β] hvS a hη hFs).mp hposQ
    obtain ⟨h0,h1⟩ := affine_two_point_coefficients α β r s hrs a heR heS
    have he : g • affineDifferential α β=algebraMap K field (a 2) • affineDifferential α β :=
      ha.symm.trans (affine_line_scalar α β a h0 h1)
    exact ⟨a 2,scalar_of_differential_equality (affineDifferential_ne_zero α β) g (a 2) he⟩

#print axioms double_divisor_injective
#print axioms affine_contact_constants
end
end FourCorner.ThetaAffineContactConstants
