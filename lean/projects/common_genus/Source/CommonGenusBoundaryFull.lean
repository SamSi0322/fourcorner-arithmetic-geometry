import CommonPostBranchValues
import CommonPostEllDegree

noncomputable section
namespace FourCorner.CommonGenusBoundaryFull
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CommonPostGeometricGenus CommonPostFiniteP1 CommonPostBranchFibres CommonPostBranchValues
local instance p1Integral : IsIntegral (ProjectiveLineCharts.P1 ℚ) := ProjectiveLineCharts.integral ℚ
local instance baseRatAlgebra : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- The actual canonical completion of the literal four-root field: geometric
connectedness and genus, the native finite ell map and its original field square,
its exact six closed branch fibres and their rational-point exclusion. -/
theorem prop_common_genus_boundary (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    letI := modelFieldAlgebra t
    GeometricallyConnected (CommonSchemeModel.modelToBase t h0 h1 hm) ∧
    IsProper (CommonSchemeModel.modelToBase t h0 h1 hm) ∧
    SmoothOfRelativeDimension 1 (CommonSchemeModel.modelToBase t h0 h1 hm) ∧
    (let c := geometricToBase t h0 h1 hm
     letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) = 9) ∧
    IsFinite (ellMap t h0 h1 hm) ∧
    (sourceFieldPoint t h0 h1 hm ≫ ellMap t h0 h1 hm =
      Spec.map (CommRingCat.ofHom (literalInclusion t)) ≫ baseFieldPoint) ∧
    IsDominant (sourceFieldPoint t h0 h1 hm) ∧
    ((commonCurve t h0 h1 hm).fromSpecStalk (genericPoint (commonCurve t h0 h1 hm)) ≫ ellMap t h0 h1 hm =
      Spec.map (CommRingCat.ofHom (CommonPostEllDegree.fieldPullback t h0 h1 hm)) ≫
        (ProjectiveLineCharts.P1 ℚ).fromSpecStalk (genericPoint (ProjectiveLineCharts.P1 ℚ))) ∧
    (letI := (CommonPostEllDegree.fieldPullback t h0 h1 hm).toAlgebra
     Module.finrank (ProjectiveLineCharts.P1 ℚ).functionField (commonCurve t h0 h1 hm).functionField = 16) ∧
    (branchPoints t).card = 6 ∧
    branchPoints t = {finiteValue 0,infinityValue,finiteValue (t-1),finiteValue (t+1),
      finiteValue (-(t-1)),finiteValue (-(t+1))} ∧
    (∀ y : closedPoints (ProjectiveLineCharts.P1 ℚ),
      y ∈ branchPoints t ↔ ∃ x : closedPoints (commonCurve t h0 h1 hm),
        ellClosed t h0 h1 hm x = y ∧
        1 < ((CommonSchemeModel.model t h0 h1 hm).placeOfPoint x).ramificationIndex (RatFunc ℚ)) ∧
    (∀ x : closedPoints (commonCurve t h0 h1 hm),
      ((CommonSchemeModel.model t h0 h1 hm).placeOfPoint x).ramificationIndex (RatFunc ℚ) =
        if ellClosed t h0 h1 hm x ∈ branchPoints t then 2 else 1) ∧
    (1 < t → ∀ p : Spec (.of ℚ) ⟶ commonCurve t h0 h1 hm,
      ellClosed t h0 h1 hm
        (CommonPostPointResidue.pointCenter (CommonSchemeModel.model t h0 h1 hm) p) ∉ branchPoints t) := by
  letI := modelFieldAlgebra t
  exact ⟨CommonSchemeModel.rational_model_geometricallyConnected t h0 h1 hm,
    CommonSchemeModel.model_proper t h0 h1 hm,
    CommonSchemeModel.model_smooth t h0 h1 hm,
    geometric_globalDifferentials_nine t h0 h1 hm,
    ellMap_isFinite t h0 h1 hm,
    generic_ellMap t h0 h1 hm,
    CommonPostGenericEll.sourceFieldPoint_dominant t h0 h1 hm,
    CommonPostEllDegree.generic_stalk_square t h0 h1 hm,
    CommonPostEllDegree.degree_sixteen t h0 h1 hm,
    branchPoints_card t h0 h1 hm,
    branchPoints_eq t,
    branch_locus_exact t h0 h1 hm,
    ramification_formula t h0 h1 hm,
    fun ht => rational_point_avoids_branch_fibres t ht h0 h1 hm⟩

end FourCorner.CommonGenusBoundaryFull
#print axioms FourCorner.CommonGenusBoundaryFull.prop_common_genus_boundary
#check @FourCorner.CommonGenusBoundaryFull.prop_common_genus_boundary
