import CommonPostRamification
import NormalizedModelPointRestriction
import CommonPostModelBoundary

noncomputable section
namespace FourCorner.CommonPostBranchFibres
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CommonPostGeometricGenus CommonPostFiniteP1
open NormalizedModelPointRestriction
local instance baseRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-- Closed-point transport along the actual normalization/P1 isomorphism. -/
def linePlace (y : closedPoints (ProjectiveLineCharts.P1 ℚ)) : Place ℚ (RatFunc ℚ) :=
  (NormalizedModelCover.baseModel ℚ).placeOfPoint (isoClosed NormalizedBaseP1.iso.symm y)

def linePoint (v : Place ℚ (RatFunc ℚ)) : closedPoints (ProjectiveLineCharts.P1 ℚ) :=
  isoClosed NormalizedBaseP1.iso ((NormalizedModelCover.baseModel ℚ).placeEquiv.symm v)

lemma linePlace_linePoint (v : Place ℚ (RatFunc ℚ)) : linePlace (linePoint v) = v := by
  unfold linePlace linePoint
  have he : isoClosed NormalizedBaseP1.iso.symm
      (isoClosed NormalizedBaseP1.iso ((NormalizedModelCover.baseModel ℚ).placeEquiv.symm v)) =
      (NormalizedModelCover.baseModel ℚ).placeEquiv.symm v := by
    apply Subtype.ext
    exact congrArg (fun f => f (((NormalizedModelCover.baseModel ℚ).placeEquiv.symm v).1))
      NormalizedBaseP1.iso.hom_inv_id
  rw [he]
  exact (NormalizedModelCover.baseModel ℚ).placeEquiv.apply_symm_apply v

lemma linePoint_linePlace (y : closedPoints (ProjectiveLineCharts.P1 ℚ)) :
    linePoint (linePlace y) = y := by
  unfold linePoint linePlace
  rw [← CurveModel.placeEquiv_apply,Equiv.symm_apply_apply]
  apply Subtype.ext
  exact congrArg (fun f => f y.1) NormalizedBaseP1.iso.inv_hom_id

lemma linePlace_injective : Function.Injective linePlace := by
  intro x y h
  simpa only [linePoint_linePlace] using congrArg linePoint h

lemma linePoint_injective : Function.Injective linePoint := by
  intro x y h
  simpa only [linePlace_linePoint] using congrArg linePlace h

/-- The six boundary values are actual closed points on the literal Proj P1. -/
def branchPoints (t : ℚ) : Finset (closedPoints (ProjectiveLineCharts.P1 ℚ)) :=
  (CommonFourPlaceOrders.support t).image linePoint

lemma branchPoints_card (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    (branchPoints t).card = 6 := by
  rw [branchPoints,Finset.card_image_of_injective _ linePoint_injective,
    CommonFourPlaceOrders.support_card t h0 h1 hm]

lemma mem_branchPoints (t : ℚ) (y : closedPoints (ProjectiveLineCharts.P1 ℚ)) :
    y ∈ branchPoints t ↔ linePlace y ∈ CommonFourPlaceOrders.support t := by
  classical
  simp only [branchPoints,Finset.mem_image]
  constructor
  · rintro ⟨v,hv,rfl⟩
    simpa only [linePlace_linePoint] using hv
  · intro h
    exact ⟨linePlace y,h,linePoint_linePlace y⟩

/-- The closed-point map of the same native finite ell morphism. -/
def ellClosed (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (x : closedPoints (commonCurve t h0 h1 hm)) : closedPoints (ProjectiveLineCharts.P1 ℚ) := by
  haveI := ellMap_isFinite t h0 h1 hm
  refine ⟨ellMap t h0 h1 hm x.1,?_⟩
  change IsClosed {ellMap t h0 h1 hm x.1}
  simpa only [Set.image_singleton] using (ellMap t h0 h1 hm).isClosedMap {x.1} x.2

/-- The actual native ell fibre is exactly restriction of the chosen source place. -/
theorem ellClosed_place (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := modelFieldAlgebra t
    ∀ x : closedPoints (commonCurve t h0 h1 hm),
      linePlace (ellClosed t h0 h1 hm x) =
        ((CommonSchemeModel.model t h0 h1 hm).placeOfPoint x).restrict (RatFunc ℚ) := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  intro x
  have h := NormalizedModelPointRestriction.point_restrict ℚ (CommonLiteralField.field ℚ t) x
  refine (congrArg (NormalizedModelCover.baseModel ℚ).placeOfPoint ?_).trans h.symm
  apply Subtype.ext
  change NormalizedBaseP1.iso.inv (ellMap t h0 h1 hm x.1) = _
  have he : ellMap t h0 h1 hm ≫ NormalizedBaseP1.iso.inv =
      NormalizedModelCover.cover ℚ (CommonLiteralField.field ℚ t) := by
    set_option backward.isDefEq.respectTransparency false in
      simp only [ellMap,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  exact congrArg (fun f => f x.1) he

/-- Ramification at every actual closed source point of the native finite cover. -/
theorem ramification_formula (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := modelFieldAlgebra t
    ∀ x : closedPoints (commonCurve t h0 h1 hm),
      ((CommonSchemeModel.model t h0 h1 hm).placeOfPoint x).ramificationIndex (RatFunc ℚ) =
        if ellClosed t h0 h1 hm x ∈ branchPoints t then 2 else 1 := by
  letI := modelFieldAlgebra t
  intro x
  rw [CommonPostRamification.ramificationIndex_formula h0 h1 hm]
  have hp : (ellClosed t h0 h1 hm x ∈ branchPoints t) ↔
      ((CommonSchemeModel.model t h0 h1 hm).placeOfPoint x).restrict (RatFunc ℚ) ∈ CommonFourPlaceOrders.support t := by
    rw [mem_branchPoints,ellClosed_place]
  by_cases h : ((CommonSchemeModel.model t h0 h1 hm).placeOfPoint x).restrict (RatFunc ℚ) ∈ CommonFourPlaceOrders.support t
  · rw [if_pos h,if_pos (hp.mpr h)]
  · rw [if_neg h,if_neg (fun hy => h (hp.mp hy))]

/-- Exactly the six actual P1 points are images of ramified closed source points. -/
theorem branch_locus_exact (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := modelFieldAlgebra t
    ∀ y : closedPoints (ProjectiveLineCharts.P1 ℚ),
      y ∈ branchPoints t ↔ ∃ x : closedPoints (commonCurve t h0 h1 hm),
        ellClosed t h0 h1 hm x = y ∧
        1 < ((CommonSchemeModel.model t h0 h1 hm).placeOfPoint x).ramificationIndex (RatFunc ℚ) := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  intro y
  constructor
  · intro hy
    obtain ⟨w,hw⟩ := Place.exists_restrict_eq (M := CommonLiteralField.field ℚ t) (linePlace y)
    let x := (CommonSchemeModel.model t h0 h1 hm).placeEquiv.symm w
    have hx : (CommonSchemeModel.model t h0 h1 hm).placeOfPoint x = w :=
      (CommonSchemeModel.model t h0 h1 hm).placeEquiv.apply_symm_apply w
    have hxy : ellClosed t h0 h1 hm x = y := by
      apply linePlace_injective
      rw [ellClosed_place,hx,hw]
    refine ⟨x,hxy,?_⟩
    rw [ramification_formula,hxy,if_pos hy]
    norm_num
  · rintro ⟨x,rfl,hx⟩
    rw [ramification_formula] at hx
    split_ifs at hx with h
    · exact h
    · omega

/-- No actual rational point of the same D_t lies over any of the six branch values. -/
theorem rational_point_avoids_branch_fibres (t : ℚ) (ht : 1 < t)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := modelFieldAlgebra t
    ∀ p : Spec (.of ℚ) ⟶ commonCurve t h0 h1 hm,
      ellClosed t h0 h1 hm
        (CommonPostPointResidue.pointCenter (CommonSchemeModel.model t h0 h1 hm) p) ∉ branchPoints t := by
  letI := modelFieldAlgebra t
  intro p h
  rw [mem_branchPoints,ellClosed_place] at h
  have hn := CommonPostModelBoundary.actual_model_point_avoids_boundary t ht h0 h1 hm p
  exact hn h

end FourCorner.CommonPostBranchFibres
#print axioms FourCorner.CommonPostBranchFibres.ellClosed_place
#print axioms FourCorner.CommonPostBranchFibres.branchPoints_card

#print axioms FourCorner.CommonPostBranchFibres.ramification_formula
#print axioms FourCorner.CommonPostBranchFibres.branch_locus_exact
#print axioms FourCorner.CommonPostBranchFibres.rational_point_avoids_branch_fibres
