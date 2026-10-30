import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesDet
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsInvertible (Scheme.Modules.det n M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback n U M
  obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (U : Scheme.{u}) n
  exact ⟨U, hxU, ⟨e₁ ≪≫ (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).mapIso e ≪≫ e₂⟩⟩
