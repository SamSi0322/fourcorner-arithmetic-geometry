import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_pullbackModuleComparison_locallySurjective
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_locallySurjective
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X X' : Scheme.{u}} (f : X' ⟶ X) {I : X.IdealSheafData} (hI : I.IsInvertible)
    (hI' : (I.comap f).IsInvertible) : IsIso (I.pullbackModuleComparison f) :=
  Scheme.Modules.IsInvertible.isIso_of_locallySurjective
    (Scheme.Modules.IsInvertible.pullback f hI.isInvertible_module) hI'.isInvertible_module
    (I.pullbackModuleComparison f)
    (Scheme.IdealSheafData.pullbackModuleComparison_locallySurjective f I)
