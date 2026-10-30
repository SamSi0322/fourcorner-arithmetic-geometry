import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import ThetaCoverClassPortable.Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution {X X' : Scheme.{u}} (f : X' ⟶ X) {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj I.invModule ≅ (I.comap f).invModule) := by
  have hM₀ : Scheme.Modules.IsInvertible I.module := hI.isInvertible_module
  have hM : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback f).obj I.module) :=
    Scheme.Modules.IsInvertible.pullback f hM₀
  have hM' : Scheme.Modules.IsInvertible (I.comap f).module := hI'.isInvertible_module
  haveI : IsIso (I.pullbackModuleComparison f) :=
    Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hI hI'
  obtain ⟨e₁⟩ := Scheme.Modules.IsInvertible.pullback_dual f hM₀
  obtain ⟨e₂⟩ := CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit
    (asIso (I.pullbackModuleComparison f)) (Scheme.Modules.IsInvertible.dual hM).2
    (Scheme.Modules.IsInvertible.dual hM').2
  exact ⟨e₁ ≪≫ e₂⟩
