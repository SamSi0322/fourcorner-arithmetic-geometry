import OddThetaDivisorClassification
import ThetaDNaturalGlobalDifferentials

noncomputable section
set_option autoImplicit false
open AlgebraicCurve AlgebraicGeometry KaehlerDifferential
namespace FourCorner.ThetaActualOddThetaClasses
open ThetaDGeometricModel DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : PerfectField K := IsAlgClosed.perfectField K
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀v : Place K field,v.DCoordGenerates := dCoordGenerates_of_isCurveOver

abbrev ActualPic := Pic K field
abbrev ActualDivisor := Divisor K field

theorem actual_canonical_ell {ω : Ω[field⁄K]} (hω : ω≠0) :
    ell (canonicalDivisorOf hω)=3 := by
  have hh:=ThetaDNativeSections.canonical_RR hω (0:ActualDivisor)
  rw [sub_zero,map_zero,ell_zero_eq_one_of_constantsAreBase
    ThetaDNativeSections.actual_constants] at hh
  omega

theorem actual_canonical_pic_degree : picDegree (canonicalClass K field)=4 := by
  obtain ⟨ω,hω⟩ := exists_ne (0:Ω[field⁄K])
  rw [canonicalClass_eq hω,picDegree_class]
  exact ThetaDNativeSections.canonical_degree_four hω

/-- Original D_Qbar, its actual native function field and genuine divisor Pic.
Only the intrinsic odd-theta class is an input; all genus/dimension/degree,
principal-divisor and canonical-form inputs are discharged by actual RR. -/
theorem actual_odd_theta_effective_unique (c : ActualPic) (hc : IsOddThetaClass c) :
    ∃ B : ActualDivisor,0≤B ∧ divisorClass B=c ∧ Divisor.degree B=2 ∧ ell B=1 ∧
      (∀E : ActualDivisor,0≤E → divisorClass E=c → E=B) ∧
      ∃(ω : Ω[field⁄K])(hω : ω≠0),ω∈regularDifferentials K field ∧
        canonicalDivisorOf hω=(2:ℕ) • B :=
  oddTheta_effective_unique actual_canonical_pic_degree (fun h=>actual_canonical_ell h) c hc

#print axioms actual_canonical_ell
#print axioms actual_canonical_pic_degree
#print axioms actual_odd_theta_effective_unique
end FourCorner.ThetaActualOddThetaClasses
