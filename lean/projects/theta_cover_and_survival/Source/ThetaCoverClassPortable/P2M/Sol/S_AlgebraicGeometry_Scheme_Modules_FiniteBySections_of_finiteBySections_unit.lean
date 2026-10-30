import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ProjSpace
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_finiteBySections_unit

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (h𝒪 : Scheme.Modules.FiniteBySections (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f := by
  haveI : IsFinite f := AlgebraicGeometry.Scheme.Modules.FiniteBySections.isFinite_of_unit f h𝒪
  exact AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_isFinite f M hM
