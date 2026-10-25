import Genus17GeometryStatement
import Genus17ValuativeUnramified
import Genus17GenericSeparable

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

/-- The geometric/morphism bundle with both generic and residue separability
explicitly included. The previous aggregate remains frozen as a separate theorem. The rational
point lifting clause is proved separately on these same frozen curve/cover definitions. -/
theorem common_genus17_geometry_complete (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := CommonPostGeometricGenus.modelFieldAlgebra t
    letI := modelFieldAlgebra t κ
    GeometricallyConnected (toBase t κ h0 h1 hm) ∧
    IsProper (toBase t κ h0 h1 hm) ∧ SmoothOfRelativeDimension 1 (toBase t κ h0 h1 hm) ∧
    IsFinite (cover t κ h0 h1 hm) ∧
    (cover t κ h0 h1 hm ≫ CommonSchemeModel.modelToBase t h0 h1 hm = toBase t κ h0 h1 hm) ∧
    ((curve t κ h0 h1 hm).fromSpecStalk (genericPoint (curve t κ h0 h1 hm)) ≫ cover t κ h0 h1 hm =
      Spec.map (CommRingCat.ofHom (coverFieldPullback t κ h0 h1 hm)) ≫
        (CommonSchemeModel.model t h0 h1 hm).C.fromSpecStalk (genericPoint (CommonSchemeModel.model t h0 h1 hm).C)) ∧
    (letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
     Module.finrank (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField = 2) ∧
    (letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
     Module.Finite (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField ∧
       Algebra.IsSeparable (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField) ∧
    (∀ x : closedPoints (curve t κ h0 h1 hm),
      ((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t) =
        (CommonSchemeModel.model t h0 h1 hm).placeOfPoint (coverClosed t κ h0 h1 hm x) ∧
      ((model t κ h0 h1 hm).placeOfPoint x).ramificationIndex (baseField t) = 1 ∧
      Module.Finite (((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t)).ResidueField
        ((model t κ h0 h1 hm).placeOfPoint x).ResidueField ∧
      Algebra.IsSeparable (((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t)).ResidueField
        ((model t κ h0 h1 hm).placeOfPoint x).ResidueField) ∧
    (let c := Genus17GeometricGenus.geometricToBase t κ h0 h1 hm
     letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
     Module.Finite (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) ∧
       Module.finrank (AlgebraicClosure ℚ) Γ(c.kaehler,⊤) = 17) ∧
    (∀ b : baseField t,
      coverFieldPullback t κ h0 h1 hm ((targetFieldEquiv t h0 h1 hm).symm b) =
        (sourceFieldEquiv t κ h0 h1 hm).symm (fieldInclusion t κ b)) ∧
    fifthRoot t κ ^ 2 = ell t κ / algebraMap ℚ (field t κ) κ := by
  letI := CommonPostGeometricGenus.modelFieldAlgebra t
  letI := modelFieldAlgebra t κ
  exact ⟨model_geometricallyConnected t κ h0 h1 hm hκ,
    model_proper t κ h0 h1 hm,model_smooth t κ h0 h1 hm,
    cover_isFinite t κ h0 h1 hm,cover_overQ t κ h0 h1 hm,
    cover_generic_stalk_square t κ h0 h1 hm,cover_degree_two t κ h0 h1 hm hκ,
    cover_generic_finite_separable t κ h0 h1 hm hκ,
    cover_valuatively_unramified t κ h0 h1 hm hκ,
    Genus17GeometricGenus.geometric_globalDifferentials_seventeen t κ h0 h1 hm hκ,
    cover_function_preservation t κ h0 h1 hm,fifthRoot_sq_literal t κ⟩
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.common_genus17_geometry_complete
#check @FourCorner.Genus17Geometry.common_genus17_geometry_complete
