import ThetaCoverClassPortable.ThetaCoverBoundaryOrders

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaCoverDivisor
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaCoverFunctions
open ThetaCoverPoleBound ThetaCoverBoundaryPoints ThetaCoverBoundaryOrders
open ThetaDCanonicalInfinityDivisor DivisorPicClassification
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

 theorem infinitySum_effective : 0 ≤ infinitySum := by
  intro w
  rw [infinitySum_apply]
  split_ifs <;> norm_num

/-- h uses the affine C0=C0_homogeneous/Z² already; its all-place divisor
therefore has exactly ONE subtraction of twice the full infinity divisor. -/
theorem actual_divisor_h :
    principalDivisor h h_ne_zero=(2:ℕ) • boundarySum-(2:ℕ) • infinitySum := by
  let T : Divisor K field := principalDivisor h h_ne_zero+(2:ℕ) • infinitySum-(2:ℕ) • boundarySum
  have hT : 0≤T := by
    intro w
    change 0 ≤ T w
    simp only [T,Finsupp.sub_apply,Finsupp.add_apply,principalDivisor_apply,
      Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,boundarySum_apply]
    by_cases hw : ∃e,place e=w
    · rw [if_pos hw]
      obtain ⟨e,rfl⟩ := hw
      have hh := boundary_h_order e
      have hH := infinitySum_effective (place e)
      simp only [Finsupp.zero_apply] at hH
      omega
    · rw [if_neg hw]
      have hh := h_all_place_bound w
      omega
  have hd : Divisor.degree T=0 := by
    simp only [T,map_sub,map_add,map_nsmul,degree_principalDivisor,
      degree_infinitySum,degree_boundarySum]
    norm_num
  have hz := divisor_zero_of_nonnegative_degree_zero T hT hd
  change principalDivisor h h_ne_zero+(2:ℕ) • infinitySum-(2:ℕ) • boundarySum=0 at hz
  exact eq_sub_iff_add_eq.mpr (sub_eq_zero.mp hz)

/-- The geometric covering class in the REAL divisor Picard quotient.
No represented-Jacobian or rational-point identification is built into this name. -/
def geometricClass : Pic K field := divisorClass (boundarySum-infinitySum)

 theorem degree_class_zero : picDegree geometricClass=0 := by
  rw [geometricClass,picDegree_class,map_sub,degree_boundarySum,degree_infinitySum]
  norm_num

 theorem class_two_torsion : (2:ℕ) • geometricClass=0 := by
  change (2:ℕ) • divisorClass (boundarySum-infinitySum)=0
  have hp : ((2:ℕ) • (boundarySum-infinitySum)).IsPrincipal := by
    refine ⟨h,h_ne_zero,fun w=>?_⟩
    have hh:=congrArg (fun D : Divisor K field=>D w) actual_divisor_h
    rw [principalDivisor_apply] at hh
    simpa only [nsmul_sub] using hh.symm
  change divisorClass ((2:ℕ) • (boundarySum-infinitySum))=0
  exact (QuotientAddGroup.eq_zero_iff _).mpr hp

#print axioms actual_divisor_h
#print axioms class_two_torsion
end FourCorner.ThetaCoverDivisor
