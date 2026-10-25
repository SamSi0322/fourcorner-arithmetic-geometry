import Genus17GenericCover

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve CategoryTheory
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- Every element of the original ordered four-root field pulls back by the
native cover to its literal inclusion in the fifth-root field. -/
theorem cover_function_preservation (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (b : baseField t) :
    coverFieldPullback t κ h0 h1 hm ((targetFieldEquiv t h0 h1 hm).symm b) =
      (sourceFieldEquiv t κ h0 h1 hm).symm (fieldInclusion t κ b) := by
  change (sourceFieldEquiv t κ h0 h1 hm).symm
    (fieldInclusion t κ ((targetFieldEquiv t h0 h1 hm) ((targetFieldEquiv t h0 h1 hm).symm b))) = _
  rw [RingEquiv.apply_symm_apply]

theorem cover_ell_preservation (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    coverFieldPullback t κ h0 h1 hm ((targetFieldEquiv t h0 h1 hm).symm (CommonLiteralField.ell K t)) =
      (sourceFieldEquiv t κ h0 h1 hm).symm (ell t κ) :=
  cover_function_preservation t κ h0 h1 hm _

theorem cover_orderedRoot_preservation (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (i : Fin 4) :
    coverFieldPullback t κ h0 h1 hm ((targetFieldEquiv t h0 h1 hm).symm (CommonLiteralField.root K t i)) =
      (sourceFieldEquiv t κ h0 h1 hm).symm (orderedRoot t κ i) :=
  cover_function_preservation t κ h0 h1 hm _

theorem fifthRoot_function_equation (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    ((sourceFieldEquiv t κ h0 h1 hm).symm (fifthRoot t κ))^2 =
      (sourceFieldEquiv t κ h0 h1 hm).symm (ell t κ) /
        (sourceFieldEquiv t κ h0 h1 hm).symm (algebraMap K (field t κ) κ) := by
  rw [← map_pow,fifthRoot_sq_literal,map_div₀]

/-- The native morphism between these exact rational models is over Q. -/
theorem cover_overQ (t κ : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    cover t κ h0 h1 hm ≫ CommonSchemeModel.modelToBase t h0 h1 hm = toBase t κ h0 h1 hm := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.cover_function_preservation
#print axioms FourCorner.Genus17Geometry.cover_ell_preservation
#print axioms FourCorner.Genus17Geometry.cover_orderedRoot_preservation
#print axioms FourCorner.Genus17Geometry.fifthRoot_function_equation
#print axioms FourCorner.Genus17Geometry.cover_overQ
