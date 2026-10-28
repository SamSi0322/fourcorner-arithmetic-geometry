import ThetaContactPairFrames

namespace FourCorner.ThetaContactLSpaceGeometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDActualDifferential
open ThetaRegularFunctionDifferential ThetaContactDifferentialDivisors
open ThetaCanonicalLinePointValues ThetaActualLineDifferentials
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

/-- ALL actual places occur in the LSpace inequality, including infinity. -/
theorem lSpace_smul_order_bound (B : Divisor K field) {η : Ω[field⁄K]} (hη : η≠0)
    (hcan : canonicalDivisorOf hη=(2:ℕ) • B) (g : field) (hg : g∈LSpace B) (hg0 : g≠0)
    (w : Place K field) : B w≤w.ordDifferential (g • η) := by
  have hor : ∀v : Place K field,-B v≤v.ord g := (mem_lSpace_iff_ord.mp hg).resolve_left hg0
  have hk := congrArg (fun D : Divisor K field=>D w) hcan
  rw [canonicalDivisorOf_apply] at hk
  simp only [two_smul,Finsupp.add_apply] at hk
  have he := w.ordDifferential_smul hg0 (ThetaContactDifferentialDivisors.coefficient_ne_zero hη w)
  have hh := hor w
  omega

 theorem lSpace_smul_regular (B : Divisor K field) (hB : 0≤B) {η : Ω[field⁄K]} (hη : η≠0)
    (hcan : canonicalDivisorOf hη=(2:ℕ) • B) (g : field) (hg : g∈LSpace B) :
    g • η∈regularDifferentials K field := by
  by_cases hg0 : g=0
  · rw [hg0,zero_smul]
    exact (regularDifferentials K field).zero_mem
  · intro w
    have hreg : 0≤w.ordDifferential (g • η) :=
      (hB w).trans (lSpace_smul_order_bound B hη hcan g hg hg0 w)
    have hn := ThetaContactDifferentialDivisors.coefficient_ne_zero (smul_ne_zero hg0 hη) w
    refine ⟨coefficient w (g • η),w.mem_of_ord_nonneg hn hreg,?_⟩
    exact (w.differentialCoeff_smul_dCoord _).symm

 theorem affine_two_point_coefficients (α β r s : K) (hrs : r≠s) (a : Fin 3 → K)
    (hR : a 0*r+a 1+a 2*(α*r+β)=0) (hS : a 0*s+a 1+a 2*(α*s+β)=0) :
    a 0= -a 2*α ∧ a 1= -a 2*β := by
  have hm : (a 0+a 2*α)*(r-s)=0 := by linear_combination hR-hS
  have h0 : a 0+a 2*α=0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hrs)
  constructor
  · linear_combination h0
  · linear_combination hR-r*h0

 theorem vertical_two_point_coefficients (t r s : K) (hrs : r≠s) (a : Fin 3 → K)
    (hR : a 0*(t*r)+a 1*r+a 2=0) (hS : a 0*(t*s)+a 1*s+a 2=0) :
    a 1= -a 0*t ∧ a 2=0 := by
  have hm : (a 0*t+a 1)*(r-s)=0 := by linear_combination hR-hS
  have h1 : a 0*t+a 1=0 := (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hrs)
  constructor
  · linear_combination h1
  · linear_combination hR-r*h1

 theorem affine_line_scalar (α β : K) (a : Fin 3 → K)
    (h0 : a 0= -a 2*α) (h1 : a 1= -a 2*β) :
    lineDifferential a=algebraMap K field (a 2) • affineDifferential α β := by
  rw [line_Z_factor]
  unfold ZEquation
  rw [h0,h1]
  rw [affineDifferential,affineGlobalSection_germ]
  simp only [smul_smul]
  rw [affineFunction_times_y]
  congr 1
  simp only [map_neg,map_mul]
  ring

 theorem vertical_line_scalar (t : K) (a : Fin 3 → K)
    (h1 : a 1= -a 0*t) (h2 : a 2=0) :
    lineDifferential a=algebraMap K field (a 0) • verticalDifferential t := by
  rw [line_Z_factor]
  unfold ZEquation
  rw [h1,h2]
  rw [verticalDifferential,verticalGlobalSection_germ,smul_smul]
  congr 1
  simp only [verticalFunction,map_zero,map_neg,map_mul]
  ring

/-- Nonzero actual differentials cancel the F-action, with base-K scalars
converted by the TRUE structural algebra map. -/
theorem scalar_of_differential_equality {η : Ω[field⁄K]} (hη : η≠0) (g : field) (c : K)
    (he : g • η=algebraMap K field c • η) : algebraMap K field c=g := by
  have hh : (g-algebraMap K field c) • η=0 := by rw [sub_smul,he,sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_right hη)).symm

#print axioms lSpace_smul_order_bound
#print axioms lSpace_smul_regular
#print axioms affine_two_point_coefficients
#print axioms vertical_two_point_coefficients
#print axioms affine_line_scalar
#print axioms vertical_line_scalar
end
end FourCorner.ThetaContactLSpaceGeometry
