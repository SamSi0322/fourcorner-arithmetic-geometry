import ThetaCoverClassPortable.ThetaCoverDivisor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaCoverAllOrders
open ThetaDGeometricModel ThetaCoverFunctions ThetaCoverBoundaryPoints ThetaCoverBoundaryOrders
open ThetaCoverDivisor ThetaDCanonicalInfinityDivisor
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
attribute [local instance] Classical.propDecidable

 theorem boundary_infinity_disjoint (e : Signs) : infinitySum (place e)=0 := by
  have hh:=congrArg (fun D : Divisor K field=>D (place e)) actual_divisor_h
  simp only [DivisorPicClassification.principalDivisor_apply,Finsupp.sub_apply,
    Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,boundarySum_apply] at hh
  rw [if_pos (show ∃d,place d=place e from ⟨e,rfl⟩)] at hh
  have hb:=boundary_h_order e
  have hH:=infinitySum_effective (place e)
  simp only [Finsupp.zero_apply] at hH
  omega

 theorem boundary_order_exact (e : Signs) : (place e).ord h=2 := by
  have hh:=congrArg (fun D : Divisor K field=>D (place e)) actual_divisor_h
  simp only [DivisorPicClassification.principalDivisor_apply,Finsupp.sub_apply,
    Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,boundarySum_apply,boundary_infinity_disjoint] at hh
  rw [if_pos (show ∃d,place d=place e from ⟨e,rfl⟩)] at hh
  omega

/-- Exact orders at EVERY actual native place, including the four original
infinity points and excluding any uncontrolled additional zero or pole. -/
theorem all_orders_h (w : Place K field) :
    w.ord h=if ∃e,place e=w then 2 else if w∈infinityPlaces then -2 else 0 := by
  by_cases hw : ∃e,place e=w
  · rw [if_pos hw]
    obtain ⟨e,rfl⟩ := hw
    exact boundary_order_exact e
  · rw [if_neg hw]
    have hh:=congrArg (fun D : Divisor K field=>D w) actual_divisor_h
    simp only [DivisorPicClassification.principalDivisor_apply,Finsupp.sub_apply,
      Finsupp.smul_apply,nsmul_eq_mul,Nat.cast_ofNat,boundarySum_apply,infinitySum_apply,if_neg hw] at hh
    split_ifs at * <;> omega

 theorem each_infinity_order (a : ThetaDFourInfinityPlaces.Parameters) :
    (ThetaDFourInfinityPlaces.place a).ord h= -2 := by
  rw [all_orders_h]
  have hi : ThetaDFourInfinityPlaces.place a∈infinityPlaces :=
    (mem_infinityPlaces _).mpr ⟨a,rfl⟩
  have hn : ¬∃e,place e=ThetaDFourInfinityPlaces.place a := by
    rintro ⟨e,he⟩
    have hh:=boundary_infinity_disjoint e
    rw [he,infinitySum_apply,if_pos hi] at hh
    norm_num at hh
  rw [if_neg hn,if_pos hi]

#print axioms all_orders_h
#print axioms each_infinity_order
end FourCorner.ThetaCoverAllOrders
