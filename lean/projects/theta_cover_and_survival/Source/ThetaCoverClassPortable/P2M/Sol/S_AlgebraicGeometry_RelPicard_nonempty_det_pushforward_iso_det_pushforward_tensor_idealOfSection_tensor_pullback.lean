import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesDet
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Hom LocallyOfFiniteType Spec Scheme smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData Scheme.Modules.IsLocallyFreeOfRank Scheme.Modules.exteriorPower Scheme.Modules.det Scheme.Modules.nonempty_det_succ_iso_det_tensor_of_shortExact Scheme.Modules.IsLocallyFreeOfRank.of_iso Scheme.Hom.isInvertible_ker_of_comp_eq_id" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforward Modules.pullback Hom Modules Modules.IsInvertible TwoAffineOpenCover Modules.IsLocallyFreeOfRank Modules.exteriorPower Modules.det Modules.nonempty_det_succ_iso_det_tensor_of_shortExact Modules.IsLocallyFreeOfRank.of_iso Hom.isInvertible_ker_of_comp_eq_id" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback Hom IsInvertible IsLocallyFreeOfRank exteriorPower det tensor nonempty_det_succ_iso_det_tensor_of_shortExact IsLocallyFreeOfRank.of_iso" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback exists_trivialization tensor" end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.of_iso' {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (h : Scheme.Modules.IsInvertible M) : Scheme.Modules.IsInvertible N := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨eU⟩⟩ := h.exists_trivialization x
  exact ⟨U, hxU, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ eU⟩⟩

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (p : T ⟶ pullback c t) (hp : p ≫ pullback.snd c t = 𝟙 T)
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (F ⊗ p.ker.module))).H0 = n)
    (hfib' : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n + 1) :
    Nonempty (Scheme.Modules.det (n + 1) ((Scheme.Modules.pushforward (pullback.snd c t)).obj F) ≅
      Scheme.Modules.det n ((Scheme.Modules.pushforward (pullback.snd c t)).obj (F ⊗ p.ker.module)) ⊗
        (Scheme.Modules.pullback p).obj F) := by

  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c t inferInstance
  have hI : p.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp
  have hFI : Scheme.Modules.IsInvertible (F ⊗ p.ker.module) := hF.tensor hI.isInvertible_module

  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_shortExact_pushforward_tensor_idealOfSection_of_forall_fibre R c ε h𝔉 t p hp F hF n hfib
  have h₁ : Scheme.Modules.IsLocallyFreeOfRank n S.X₁ :=
    Scheme.Modules.IsLocallyFreeOfRank.of_iso e₁.symm
      (isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t (F ⊗ p.ker.module) hFI n hfib)
  have h₂ : Scheme.Modules.IsLocallyFreeOfRank (n + 1) S.X₂ :=
    Scheme.Modules.IsLocallyFreeOfRank.of_iso e₂.symm
      (isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t F hF (n + 1) hfib')
  have h₃ : Scheme.Modules.IsInvertible S.X₃ :=
    Scheme.Modules.IsInvertible.of_iso' e₃.symm (hF.pullback p)
  obtain ⟨e⟩ := Scheme.Modules.nonempty_det_succ_iso_det_tensor_of_shortExact S hS h₁ h₂ h₃
  exact ⟨(Scheme.Modules.exteriorPower T (n + 1)).mapIso e₂.symm ≪≫ e ≪≫
    ((Scheme.Modules.exteriorPower T n).mapIso e₁ ⊗ᵢ e₃)⟩
