import ThetaCoverClassPortable.ThetaDFourInfinityPlaces

namespace FourCorner.ThetaDCanonicalInfinityDivisor
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDActualDifferential ThetaDGlobalCanonicalCandidate
open ThetaDFourInfinityPlaces
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver

/-- Actual places of the four actual original points at infinity. -/
def infinityPlaces : Finset (Place K field) := Finset.univ.image place

 theorem infinityPlaces_card : infinityPlaces.card=4 := by
  rw [infinityPlaces,Finset.card_image_of_injective _ place_injective]
  simpa using ThetaDInfinityPoints.parameters_card

 theorem mem_infinityPlaces (w : Place K field) : w∈infinityPlaces ↔ ∃a : Parameters,place a=w := by
  simp [infinityPlaces]

/-- The Weil divisor supported at these actual geometric points, each
with multiplicity ONE. The equality with the canonical divisor is proved below. -/
def infinitySum : Divisor K field := ∑w∈infinityPlaces,Finsupp.single w 1

 theorem infinitySum_apply (w : Place K field) : infinitySum w=if w∈infinityPlaces then 1 else 0 := by
  simp [infinitySum,Finsupp.sum_apply,Finsupp.single_apply,eq_comm]

 theorem infinitySum_le_canonical : infinitySum≤canonicalDivisorOf omega_ne_zero := by
  intro w
  rw [infinitySum_apply,canonicalDivisorOf_apply]
  by_cases hw : w∈infinityPlaces
  · rw [if_pos hw]
    obtain ⟨a,rfl⟩ := (mem_infinityPlaces w).mp hw
    have hh := place_order_positive a
    omega
  · rw [if_neg hw]
    exact all_orders_nonnegative w

 theorem degree_infinitySum : Divisor.degree infinitySum=4 := by
  simp [infinitySum,map_sum,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed,infinityPlaces_card]

 theorem degree_eq_sum (D : Divisor K field) : Divisor.degree D=∑w∈D.support,D w := by
  simp [Divisor.degree,Finsupp.liftAddHom_apply,Finsupp.sum,IsCurveOver.deg_eq_one_of_isAlgClosed]

 theorem divisor_zero_of_nonnegative_degree_zero (D : Divisor K field)
    (hD : 0≤D) (hd : Divisor.degree D=0) : D=0 := by
  apply Finsupp.ext
  intro w
  by_cases hw : w∈D.support
  · have hs : (∑v∈D.support,D v)=0 := (degree_eq_sum D).symm.trans hd
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun v _=>hD v)).mp hs w hw
    exact hh
  · exact Finsupp.notMem_support_iff.mp hw

/-- The actual dx/F_y canonical divisor on original D_Qbar is EXACTLY the
sum of its four displayed actual infinity points, each with order one.
This follows from actual local regularity and the independently proved degree4. -/
theorem canonical_divisor_exact : canonicalDivisorOf omega_ne_zero=infinitySum := by
  have hD : (0 : Divisor K field)≤canonicalDivisorOf omega_ne_zero-infinitySum :=
    sub_nonneg.mpr infinitySum_le_canonical
  have hd : Divisor.degree (canonicalDivisorOf omega_ne_zero-infinitySum)=0 := by
    rw [map_sub,canonical_candidate_degree_four,degree_infinitySum]
    norm_num
  exact sub_eq_zero.mp (divisor_zero_of_nonnegative_degree_zero _ hD hd)

 theorem all_orders_exact (w : Place K field) :
    w.ordDifferential omega=if w∈infinityPlaces then 1 else 0 := by
  rw [←canonicalDivisorOf_apply omega_ne_zero,canonical_divisor_exact,infinitySum_apply]

 theorem displayed_infinity_order_one (a : Parameters) : (place a).ordDifferential omega=1 := by
  rw [all_orders_exact,if_pos ((mem_infinityPlaces _).mpr ⟨a,rfl⟩)]

#print axioms infinityPlaces_card
#print axioms infinitySum_le_canonical
#print axioms canonical_divisor_exact
#print axioms all_orders_exact
#print axioms displayed_infinity_order_one
end
end FourCorner.ThetaDCanonicalInfinityDivisor
