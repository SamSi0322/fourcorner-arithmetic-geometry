import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
universe u
namespace TwoChartCech
/-- For modules over an actual field, arbitrary field extensions preserve
kernel finrank. No finite-dimensionality or map-surjectivity is assumed. -/
theorem finrank_ker_baseChange_eq_of_field_extension
    {R : Type u} [Field R] {C0 C1 : Type u}
    [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (k : Type u) [Field k] [Algebra R k]
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank k (LinearMap.ker (d.baseChange k)) =
      Module.finrank K (LinearMap.ker (d.baseChange K)) := by
  obtain ⟨e0⟩ := P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial.TwoChartCech.Sections.BC.nonempty_ker_baseChange_equiv_of_flat (A := k) d
  obtain ⟨e1⟩ := P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial.TwoChartCech.Sections.BC.nonempty_ker_baseChange_equiv_of_flat (A := K) d
  rw [e0.finrank_eq,e1.finrank_eq,Module.finrank_baseChange,Module.finrank_baseChange]
end TwoChartCech
