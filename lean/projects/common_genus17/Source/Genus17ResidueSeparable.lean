import Genus17PointMap

noncomputable section
namespace FourCorner.Genus17Geometry
open AlgebraicGeometry AlgebraicCurve
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

/-- The residue extension in the actual restricted-place morphism is finite
and separable. Together with the proved index one this includes the residue
condition in valuative unramifiedness, rather than only its numerical index. -/
theorem cover_residue_finite_separable (t κ : K) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1)
    (w : Place K (field t κ)) :
    Module.Finite (w.restrict (baseField t)).ResidueField w.ResidueField ∧
      Algebra.IsSeparable (w.restrict (baseField t)).ResidueField w.ResidueField := by
  letI := finite_over_line t κ h0 h1 hm
  letI : IsCurveOver K (field t κ) := RatFuncFiniteExtension.isCurveOver_of_charZero K (field t κ)
  letI := IsCurveOver.instFiniteResidue w
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Module.Finite (w.restrict (baseField t)).ResidueField w.ResidueField :=
    FiniteDimensional.right K _ _
  haveI : CharZero (w.restrict (baseField t)).ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K (w.restrict (baseField t)).ResidueField).injective
  exact ⟨inferInstance,inferInstance⟩
end FourCorner.Genus17Geometry
#print axioms FourCorner.Genus17Geometry.cover_residue_finite_separable
