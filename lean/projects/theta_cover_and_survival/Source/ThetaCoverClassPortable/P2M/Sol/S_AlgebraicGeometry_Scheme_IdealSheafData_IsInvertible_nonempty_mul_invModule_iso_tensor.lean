import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Definitions.Def_PresheafOfModules_InternalHom
import ThetaCoverClassPortable.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
attribute [-instance] PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"
namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.IdealSheafData Scheme.Modules.dual Scheme.Modules.IsInvertible Scheme.IdealSheafData.IsInvertible Scheme.Modules.IsInvertible.dual Scheme.Modules.IsInvertible.dual_tensor"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules IdealSheafData Modules.dual Modules.IsInvertible IdealSheafData.IsInvertible Modules.IsInvertible.dual Modules.IsInvertible.dual_tensor"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "tensor dual IsInvertible IsInvertible.tensor IsInvertible.dual IsInvertible.dual_tensor"
namespace InverseUnique
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

noncomputable def inverseUnique {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {L M M' : C} (e : L ⊗ M ≅ 𝟙_ C) (e' : L ⊗ M' ≅ 𝟙_ C) : M ≅ M' :=
  (λ_ M).symm ≪≫ (e'.symm ⊗ᵢ Iso.refl M) ≪≫ (β_ L M' ⊗ᵢ Iso.refl M) ≪≫ α_ M' L M ≪≫
    (Iso.refl M' ⊗ᵢ e) ≪≫ ρ_ M'

end AlgebraicGeometry.Scheme.Modules.InverseUnique

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.InverseUnique AlgebraicGeometry.Scheme.IdealSheafData in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {I J : X.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Nonempty ((I * J).invModule ≅ I.invModule ⊗ J.invModule) := by

  obtain ⟨e⟩ := IsInvertible.nonempty_mul_module_iso_tensor hI hJ
  have hA : Scheme.Modules.IsInvertible (I * J).module := IsInvertible.isInvertible_module (hI.mul hJ)
  have hB : Scheme.Modules.IsInvertible (I.module ⊗ J.module) :=
    (IsInvertible.isInvertible_module hI).tensor (IsInvertible.isInvertible_module hJ)
  obtain ⟨eA⟩ := (Scheme.Modules.IsInvertible.dual hA).2
  obtain ⟨eB⟩ := (Scheme.Modules.IsInvertible.dual hB).2

  have eB' : (I * J).module ⊗ Scheme.Modules.dual (I.module ⊗ J.module) ≅ 𝟙_ X.Modules :=
    (e ⊗ᵢ Iso.refl _) ≪≫ eB
  obtain ⟨e11⟩ := Scheme.Modules.IsInvertible.dual_tensor (IsInvertible.isInvertible_module hI)
    (IsInvertible.isInvertible_module hJ)
  exact ⟨inverseUnique eA eB' ≪≫ e11⟩
