import ThetaCoverClassPortable.ThetaCoverGaloisDescentData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaCoverPic0
open ThetaDGeometricModel ThetaCoverFunctions ThetaCoverBoundaryPoints ThetaCoverDivisor ThetaCoverClass
open ThetaDCanonicalInfinityDivisor DivisorPicClassification ThetaCoverGaloisDescentData
open ThetaGaloisSchemeField ThetaGaloisFieldAction ThetaCoverContacts
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

def zeroDegreeDivisor : Divisor.degZero (K:=K) (F:=field) :=
  ⟨boundarySum-infinitySum,by rw [Divisor.mem_degZero,map_sub,degree_boundarySum,degree_infinitySum];norm_num⟩

/-- The class in the NATIVE degree-zero divisor class group itself. It is
not asserted to be a point of any designated or represented Jacobian. -/
def delta : Pic0 K field := Pic0.mk zeroDegreeDivisor

 theorem delta_ne_zero : delta≠0 := by
  intro hz
  have hp := (QuotientAddGroup.eq_zero_iff zeroDegreeDivisor).mp hz
  have hp' : (boundarySum-infinitySum).IsPrincipal := hp
  apply geometric_class_nonzero
  exact (QuotientAddGroup.eq_zero_iff _).mpr hp'

 theorem delta_two_torsion : (2:ℕ) • delta=0 := by
  change QuotientAddGroup.mk ((2:ℕ) • zeroDegreeDivisor)=0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  change ((2:ℕ) • (boundarySum-infinitySum)).IsPrincipal
  refine ⟨h,h_ne_zero,fun w=>?_⟩
  have hh:=congrArg (fun D : Divisor K field=>D w) actual_divisor_h
  rw [principalDivisor_apply] at hh
  simpa only [nsmul_sub] using hh.symm

 theorem delta_mem_native_torsion : delta∈Pic0.torsion K field 2 := by
  rw [Pic0.mem_torsion]
  simpa only [Nat.cast_ofNat,show (2:ℤ)=1+1 from rfl,add_zsmul,one_zsmul,two_nsmul] using delta_two_torsion

def contactZeroDegreeDivisor : Divisor.degZero (K:=K) (F:=field) :=
  ⟨Bplus-Bminus,by rw [Divisor.mem_degZero,map_sub,plus_degree,minus_degree];norm_num⟩

 theorem delta_eq_actual_contacts : delta=Pic0.mk contactZeroDegreeDivisor := by
  change QuotientAddGroup.mk zeroDegreeDivisor=QuotientAddGroup.mk contactZeroDegreeDivisor
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change ((boundarySum-infinitySum)-(Bplus-Bminus)).IsPrincipal
  exact (class_eq_iff_principal_sub _ _).mp geometric_class_eq_contacts

 theorem delta_fixed (σ : Gal) : absoluteAction σ • delta=delta := by
  unfold delta
  rw [SemilinearAut.pic0_smul_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  rw [SemilinearAut.coe_degZeroSMulHom]
  change absoluteAction σ • (boundarySum-infinitySum)=boundarySum-infinitySum
  rw [smul_sub,boundary_divisor_fixed,infinity_divisor_fixed]

#print axioms delta_ne_zero
#print axioms delta_mem_native_torsion
end FourCorner.ThetaCoverPic0
