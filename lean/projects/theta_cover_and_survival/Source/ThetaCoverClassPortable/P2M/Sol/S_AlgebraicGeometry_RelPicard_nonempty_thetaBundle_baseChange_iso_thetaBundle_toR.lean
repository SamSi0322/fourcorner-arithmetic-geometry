import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesDet
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_transport_sectionTwist_baseChange_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange"

namespace ThetaKSketch

noncomputable def dualIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

end ThetaKSketch

open ThetaKSketch in
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') (r n : ℕ) :
    Nonempty (thetaBundle (baseChange R c R') (sectionBaseChange R' ε) t' M r n ≅
      thetaBundle c ε (t' ≫ specMap R R') (BaseChange.toR c ε R' M) r n) := by
  obtain ⟨iTw⟩ := RelPicard.nonempty_transport_sectionTwist_baseChange_iso R c ε R' t' r
  obtain ⟨iPush⟩ := Scheme.Modules.nonempty_pushforward_hom_comp_iso (κ c R' t')
    (pullback.snd c (t' ≫ specMap R R')) (M.L ⊗ sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r)

  have hsnd : pullback.snd (baseChange R c R') t' = (κ c R' t').hom ≫ pullback.snd c (t' ≫ specMap R R') :=
    (κ_hom_snd c R' t').symm

  let iE : picardBundle (baseChange R c R') (sectionBaseChange R' ε) t' M
      (sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r) ≅
      picardBundle c ε (t' ≫ specMap R R') (toR c ε R' M) (sectionTwist c ε (t' ≫ specMap R R') r) :=
    (Scheme.Modules.pushforwardCongr hsnd).app _ ≪≫ iPush ≪≫
      (Scheme.Modules.pushforward (pullback.snd c (t' ≫ specMap R R'))).mapIso
        (Scheme.Modules.pullbackTensorObjIso (κ c R' t').inv M.L _ ≪≫ whiskerLeftIso _ iTw)
  exact ⟨dualIso ((Scheme.Modules.exteriorPower T n).mapIso iE)⟩
