import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
universe u
namespace FourCorner.FMDUnitCohomology

/-- The actual unit-module sections are the actual structure-ring sections,
with the SAME structural base-ring action, by the identity on elements. -/
def unitSectionsRingEquiv {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (π : Y ⟶ Spec (.of R)) (U : Y.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit Y.ringCatSheaf) U
    Γ(SheafOfModules.unit Y.ringCatSheaf,U) ≃ₗ[R] Γ(Y,U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π (SheafOfModules.unit Y.ringCatSheaf) U
  exact {
    toFun := fun s => (show Γ(Y,U) from s)
    invFun := fun s => (show Γ(SheafOfModules.unit Y.ringCatSheaf,U) from s)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
end FourCorner.FMDUnitCohomology
