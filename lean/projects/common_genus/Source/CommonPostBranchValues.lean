import CommonPostBranchFibres

noncomputable section
namespace FourCorner.CommonPostBranchValues
open AlgebraicGeometry AlgebraicCurve RationalFunctionField
open CommonPostBranchFibres
set_option maxHeartbeats 1500000
local instance baseRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- The actual P1 point with finite coordinate a, transported through the
constructed isomorphism preserving the original RatFunc.X. -/
def finiteValue (a : ℚ) : closedPoints (ProjectiveLineCharts.P1 ℚ) :=
  linePoint (placeOfPoint ℚ a)
def infinityValue : closedPoints (ProjectiveLineCharts.P1 ℚ) := linePoint (placeInfty ℚ)

lemma finiteValue_place (a : ℚ) : linePlace (finiteValue a) = placeOfPoint ℚ a :=
  linePlace_linePoint _
lemma infinityValue_place : linePlace infinityValue = placeInfty ℚ := linePlace_linePoint _

/-- A coordinate certificate for the finite value, using its actual rational
function-field valuation rather than an arbitrary name for a point. -/
lemma finiteValue_order (a b : ℚ) :
    (linePlace (finiteValue a)).ord (CommonFourPlaceOrders.linear b) = if a=b then 1 else 0 := by
  rw [finiteValue_place]
  by_cases h : a=b
  · simpa only [if_pos h] using CommonFourPlaceOrders.ord_linear_finite a b
  · simpa only [if_neg h] using CommonFourPlaceOrders.ord_linear_finite a b
lemma infinityValue_order : (linePlace infinityValue).ord (RatFunc.X : RatFunc ℚ) = -1 := by
  rw [infinityValue_place]
  set_option backward.isDefEq.respectTransparency false in
    simpa only [CommonFourPlaceOrders.linear_eq,map_zero,sub_zero] using
      CommonFourPlaceOrders.ord_linear_infty (K := ℚ) 0

/-- The six native branch points are precisely the literal values in the paper. -/
theorem branchPoints_eq (t : ℚ) : branchPoints t =
    {finiteValue 0,infinityValue,finiteValue (t-1),finiteValue (t+1),
      finiteValue (-(t-1)),finiteValue (-(t+1))} := by
  ext y
  simp only [branchPoints,CommonFourPlaceOrders.support,CommonFourPlaceOrders.privatePlaces,
    Finset.mem_image,Finset.mem_insert,Finset.mem_singleton,Finset.mem_univ,true_and]
  simp only [Fin.exists_fin_succ,CommonFourPlaceOrders.branch,finiteValue,infinityValue]
  aesop
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inl rfl
end FourCorner.CommonPostBranchValues
#print axioms FourCorner.CommonPostBranchValues.branchPoints_eq
#print axioms FourCorner.CommonPostBranchValues.finiteValue_order
#print axioms FourCorner.CommonPostBranchValues.infinityValue_order
