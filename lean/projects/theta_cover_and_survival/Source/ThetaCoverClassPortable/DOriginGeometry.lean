import ThetaCoverClassPortable.DFieldCore

noncomputable section
set_option autoImplicit false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.DRationalInputs

/-- The original OD is a genuine closed section of the original D/QQ. -/
theorem origin_closedImmersion : IsClosedImmersion OD.1 :=
  isClosedImmersion_of_comp_eq_id toBase OD.1 OD.2

def originComplement : curve.Opens := by
  letI := origin_closedImmersion
  exact ⟨(Set.range OD.1)ᶜ, OD.1.isClosedEmbedding.isClosed_range.isOpen_compl⟩

@[simp] theorem mem_originComplement (x : curve) :
    x ∈ originComplement ↔ x ∉ Set.range OD.1 := Iff.rfl

end FourCorner.DRationalInputs
