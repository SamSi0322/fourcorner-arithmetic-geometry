import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_transport_sectionTwist_baseChange_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_transport_sectionTwist_baseChange_iso.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso SmoothOfRelativeDimension Scheme.Modules.pullback Scheme.Hom Spec Scheme Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.ker_fst_of_isClosedImmersion IsClosedImmersion IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules Scheme.IdealSheafData RelPicard.rigSection RelPicard.sectionIdeal Scheme.IdealSheafData.IsInvertible Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso"
p2m_open "AlgebraicGeometry"

theorem stwK5_comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero => simp [Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem stwK5_isInvertible_sectionIdeal (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (RelPicard.sectionIdeal c ε t).IsInvertible := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσq : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (RelPicard.rigSection c t ε) hσq

theorem stwK5_ker_comap_iso_inv {T P P' : Scheme.{u}} (e : P' ≅ P) (σ' : T ⟶ P') [IsClosedImmersion σ']
    (σ : T ⟶ P) (hσ : σ ≫ e.inv = σ') : σ'.ker.comap e.inv = σ.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h : σ ≫ e.inv = 𝟙 T ≫ σ' := by rw [Category.id_comp]; exact hσ
  haveI : IsIso (pullback.lift σ (𝟙 T) h) := by
    have hl : pullback.lift σ (𝟙 T) h = inv (pullback.snd e.inv σ') :=
      IsIso.eq_inv_of_inv_hom_id (pullback.lift_snd _ _ _)
    rw [hl]; infer_instance
  calc (pullback.fst e.inv σ').ker
      = (pullback.lift σ (𝟙 T) h ≫ pullback.fst e.inv σ').ker := (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = σ.ker := by rw [pullback.lift_fst]

theorem stwK5_sectionIdeal_comap_κ_inv (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (RelPicard.sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t').comap (κ c R' t').inv =
      RelPicard.sectionIdeal c ε (t' ≫ specMap R R') := by
  haveI : IsClosedImmersion (RelPicard.rigSection (baseChange R c R') t' (sectionBaseChange R' ε)) := by
    have : IsClosedImmersion (RelPicard.rigSection (baseChange R c R') t' (sectionBaseChange R' ε) ≫
        pullback.snd (baseChange R c R') t') := by
      rw [show RelPicard.rigSection (baseChange R c R') t' (sectionBaseChange R' ε) ≫
          pullback.snd (baseChange R c R') t' = 𝟙 T from pullback.lift_snd _ _ _]
      infer_instance
    exact .of_comp _ (pullback.snd (baseChange R c R') t')
  exact stwK5_ker_comap_iso_inv (κ c R' t') _ _ (rigSection_κ_inv c ε R' t')

end AlgebraicGeometry

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (κ c R' t').inv).obj
        (sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r) ≅
      sectionTwist c ε (t' ≫ specMap R R') r) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (baseChange R c R') :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hJ' : (sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t').IsInvertible :=
    stwK5_isInvertible_sectionIdeal _ _ t'
  have hJ : (sectionIdeal c ε (t' ≫ specMap R R')).IsInvertible := stwK5_isInvertible_sectionIdeal c ε _
  have hcomap : ((sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t') ^ r).comap (κ c R' t').inv =
      (sectionIdeal c ε (t' ≫ specMap R R')) ^ r := by
    rw [stwK5_comap_pow]
    exact congrArg (· ^ r) (stwK5_sectionIdeal_comap_κ_inv c ε R' t')
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso (κ c R' t').inv
    (hJ'.pow r) (hcomap ▸ hJ.pow r)
  unfold sectionTwist
  exact ⟨e ≪≫ eqToIso (by rw [hcomap])⟩
