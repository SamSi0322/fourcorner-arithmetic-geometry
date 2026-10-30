import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_PresheafOfModules_ExteriorPower
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesDet
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ThetaCoverClassPortable.P2M.Util
import ThetaCoverClassPortable.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective (f.kaehlerToSections U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen.solution
