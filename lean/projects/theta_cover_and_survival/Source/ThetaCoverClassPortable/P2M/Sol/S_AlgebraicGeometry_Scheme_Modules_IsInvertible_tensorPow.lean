import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution {X : Scheme.{u}} {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (n : ℕ) : Scheme.Modules.IsInvertible (L.tensorPow n) := by
  induction n with
  | zero =>

    simpa only [Scheme.Modules.tensorPow_zero, Scheme.Modules.tensorUnit_eq] using
      Scheme.Modules.isInvertible_unit X
  | succ n ih =>
    simpa only [Scheme.Modules.tensorPow_succ] using ih.tensor hL

#print axioms solution
