import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_fst_thetaBundle_iso_baseChange

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (M' : RigidifiedLineBundle (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
      (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (e : M'.L ≅ (BaseChange.ofR c ε R'
      (M.pullbackAlong ⟨pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R R'))), pullback.condition⟩)).L) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).obj
        (thetaBundle c ε t M r n) ≅
      thetaBundle (SmoothProperCurve.baseChange R c R') (SmoothProperCurve.sectionBaseChange R' ε)
        (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap R R')))) M' r n) := by

  let ψ : SchemeHomOver (pullback.snd t (specMap R R') ≫ specMap R R') t :=
    ⟨pullback.fst t (specMap R R'), pullback.condition⟩

  let e₁ : (toR c ε R' M').L ≅ (M.pullbackAlong ψ).L :=
    (Scheme.Modules.pullback (κ c R' (pullback.snd t (specMap R R'))).inv).mapIso e ≪≫ toR_ofR_iso c ε R' _
  obtain ⟨i₁⟩ := RelPicard.nonempty_pullback_thetaBundle_iso R c ε h𝔉 M r n hfib ψ (toR c ε R' M') e₁
  obtain ⟨i₂⟩ := RelPicard.nonempty_thetaBundle_baseChange_iso_thetaBundle_toR R c ε R'
    (pullback.snd t (specMap R R')) M' r n
  exact ⟨i₁ ≪≫ i₂.symm⟩
