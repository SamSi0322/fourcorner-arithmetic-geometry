import ThetaCoverClassPortable.KummerWeilLocal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_mem_iff_ord_nonneg
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory TopologicalSpace
namespace FourCorner.AllOrdersRegularUnits
open SmoothProperClosedPointPlaces
variable {k : Type} [Field k] {X : Scheme} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c] [IsProper c]

/-- All actual closed-point orders on an actual affine recover a true
regular section, through the intersection of native DVR stalk ranges. -/
theorem regular_of_nonnegative_orders (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) (hf : f≠0)
    (horders : letI := fieldAlgebra c
      ∀x : closedPoints X,x.val∈U → 0≤(placeOfClosedPoint c x).ord f) :
    ∃s : Γ(X,U),algebraMap Γ(X,U) X.functionField s=f := by
  letI := fieldAlgebra c
  change f∈(algebraMap Γ(X,U) X.functionField).range
  rw [AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen c U hU]
  apply Subring.mem_iInf.mpr
  intro v
  apply Subring.mem_iInf.mpr
  rintro ⟨x,hx,hcl,hr⟩
  have he : placeOfClosedPoint c ⟨x,hcl⟩=v := by
    apply Place.ext
    apply ValuationSubring.toSubring_injective
    rw [←range_stalk c ⟨x,hcl⟩,hr]
  apply (v.mem_iff_ord_nonneg hf).mpr
  rw [←he]
  exact horders ⟨x,hcl⟩ hx

/-- Converse to the true regular-unit order calculation: a nonzero native
rational function with zero order at every closed point of an actual
affine is an actual regular unit, with the prescribed native germ. -/
theorem unit_of_zero_orders (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : X.functionField) (hf : f≠0)
    (horders : letI := fieldAlgebra c
      ∀x : closedPoints X,x.val∈U → (placeOfClosedPoint c x).ord f=0) :
    ∃s : Γ(X,U)ˣ,algebraMap Γ(X,U) X.functionField (s:Γ(X,U))=f := by
  letI := fieldAlgebra c
  obtain ⟨s,hs⟩ := regular_of_nonnegative_orders c U hU f hf (fun x hx=>by rw [horders x hx])
  obtain ⟨t,ht⟩ := regular_of_nonnegative_orders c U hU f⁻¹ (inv_ne_zero hf)
    (fun x hx=>by rw [Place.ord_inv,horders x hx];rfl)
  have hst : s*t=1 := by
    apply X.germToFunctionField_injective U
    change algebraMap Γ(X,U) X.functionField _ = algebraMap Γ(X,U) X.functionField _
    rw [map_mul,map_one,hs,ht,mul_inv_cancel₀ hf]
  have hu := IsUnit.of_mul_eq_one t hst
  exact ⟨hu.unit,by rw [hu.unit_spec];exact hs⟩

#print axioms regular_of_nonnegative_orders
#print axioms unit_of_zero_orders
end FourCorner.AllOrdersRegularUnits
