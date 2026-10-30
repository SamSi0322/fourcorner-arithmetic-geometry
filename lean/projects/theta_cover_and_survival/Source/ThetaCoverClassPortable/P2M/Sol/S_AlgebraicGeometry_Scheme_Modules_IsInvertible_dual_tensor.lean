import ThetaCoverClassPortable.ReplayImports
import Mathlib.AlgebraicGeometry.Modules.Tilde
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_PresheafOfModules_InternalHom
import ThetaCoverClassPortable.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.dual Scheme.Modules.IsInvertible.dual"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules Modules.IsInvertible Modules.dual Modules.IsInvertible.dual"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsInvertible tensor dual IsInvertible.dual"
namespace InverseUnique
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique in
theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (L ⊗ M) ≅
      AlgebraicGeometry.Scheme.Modules.dual L ⊗ AlgebraicGeometry.Scheme.Modules.dual M) := by
  obtain ⟨eL⟩ := (Scheme.Modules.IsInvertible.dual hL).2
  obtain ⟨eM⟩ := (Scheme.Modules.IsInvertible.dual hM).2
  obtain ⟨eLM⟩ := (Scheme.Modules.IsInvertible.dual (hL.tensor hM)).2

  let e' : (L ⊗ M) ⊗ (Scheme.Modules.dual L ⊗ Scheme.Modules.dual M) ≅ 𝟙_ X.Modules :=
    α_ L M _ ≪≫ (Iso.refl L ⊗ᵢ ((α_ M _ _).symm ≪≫ (β_ M (Scheme.Modules.dual L) ⊗ᵢ Iso.refl _) ≪≫
      α_ _ M _ ≪≫ (Iso.refl _ ⊗ᵢ eM) ≪≫ ρ_ _)) ≪≫ eL
  exact ⟨inverseUnique eLM e'⟩
