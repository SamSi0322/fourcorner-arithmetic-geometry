import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_le
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') [IsIso f] :
    Scheme.Modules.zeroSchemeIdeal (s ≫ f) = Scheme.Modules.zeroSchemeIdeal s := by
  refine le_antisymm (Scheme.Modules.zeroSchemeIdeal_comp_le s f) ?_
  have h := Scheme.Modules.zeroSchemeIdeal_comp_le (s ≫ f) (inv f)
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
