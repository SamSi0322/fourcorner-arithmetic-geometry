import Genus17ResidueSeparable

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- Full valuative unramification data on every native closed-point fibre:
the actual target is the restricted source place, e=1, and the induced
residue-field extension is finite and separable. -/
theorem cover_valuatively_unramified (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0)
    (x : closedPoints (curve t κ h0 h1 hm)) :
    ((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t) =
      (CommonSchemeModel.model t h0 h1 hm).placeOfPoint (coverClosed t κ h0 h1 hm x) ∧
    ((model t κ h0 h1 hm).placeOfPoint x).ramificationIndex (baseField t) = 1 ∧
    Module.Finite (((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t)).ResidueField
      ((model t κ h0 h1 hm).placeOfPoint x).ResidueField ∧
    Algebra.IsSeparable (((model t κ h0 h1 hm).placeOfPoint x).restrict (baseField t)).ResidueField
      ((model t κ h0 h1 hm).placeOfPoint x).ResidueField :=
  ⟨cover_point_restrict t κ h0 h1 hm x,cover_all_closed_indices_one t κ h0 h1 hm hκ x,
    cover_residue_finite_separable t κ h0 h1 hm _⟩
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.cover_valuatively_unramified
