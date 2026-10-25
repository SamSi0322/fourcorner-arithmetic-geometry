import Genus17GenericCover

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

/-- The certified native generic-stalk extension is finite and separable;
separability is derived from characteristic zero, never assumed. -/
theorem cover_generic_finite_separable (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
    Module.Finite (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField ∧
    Algebra.IsSeparable (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField := by
  letI := (coverFieldPullback t κ h0 h1 hm).toAlgebra
  haveI : Module.Finite (CommonSchemeModel.model t h0 h1 hm).C.functionField (curve t κ h0 h1 hm).functionField :=
    FiniteDimensional.of_finrank_pos (by rw [cover_degree_two t κ h0 h1 hm hκ]; norm_num)
  haveI : CharZero (CommonSchemeModel.model t h0 h1 hm).C.functionField := by
    letI := (CommonSchemeModel.model t h0 h1 hm).functionFieldAlgebra
    exact charZero_of_injective_algebraMap
      (algebraMap K (CommonSchemeModel.model t h0 h1 hm).C.functionField).injective
  exact ⟨inferInstance,inferInstance⟩
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.cover_generic_finite_separable
