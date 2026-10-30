import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.Modules.pullback Scheme.Hom Spec Scheme Scheme.IdealSheafData.comap_top IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules Scheme.IdealSheafData RelPicard.baseChangeSnd RelPicard.rigSection RelPicard.sectionIdeal RelEffCartierDiv RelEffCartierDiv.I Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.ofPoint RelEffCartierDiv.pullbackAlong_ofPoint Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso"
p2m_open "AlgebraicGeometry"

theorem stwE5_comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero => simp [Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem stwE5_sectionIdeal_comap (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    (RelPicard.sectionIdeal c ε t).comap (RelPicard.baseChangeSnd c ψ) =
      RelPicard.sectionIdeal c ε t' := by
  have hpt : (t ≫ ε.1) ≫ c = t := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt'' : (t' ≫ ε.1) ≫ c = t' := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt' : ψ.1 ≫ t ≫ ε.1 = t' ≫ ε.1 := by rw [← Category.assoc, ψ.2]
  have key := congrArg RelEffCartierDiv.I
    (RelEffCartierDiv.pullbackAlong_ofPoint c (t ≫ ε.1) hpt ψ.1 ψ.2)
  have e₁ : RelPicard.sectionIdeal c ε t = (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I := rfl
  have e₂ : RelPicard.sectionIdeal c ε t' = (RelEffCartierDiv.ofPoint c (t' ≫ ε.1) hpt'').I := rfl
  have e₃ : (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I.comap (RelPicard.baseChangeSnd c ψ) =
      ((RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).pullbackAlong ψ.1 ψ.2).I := rfl
  rw [e₁, e₂, e₃, key]
  simp only [hpt']

theorem stwE5_isInvertible_sectionIdeal (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (RelPicard.sectionIdeal c ε t).IsInvertible := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hσq : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (RelPicard.rigSection c t ε) hσq

end AlgebraicGeometry

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (sectionTwist c ε t r) ≅ sectionTwist c ε t' r) := by
  have hJ : (sectionIdeal c ε t).IsInvertible := stwE5_isInvertible_sectionIdeal c ε t
  have hJ' : (sectionIdeal c ε t').IsInvertible := stwE5_isInvertible_sectionIdeal c ε t'
  have hcomap : ((sectionIdeal c ε t) ^ r).comap (baseChangeSnd c ψ) = (sectionIdeal c ε t') ^ r := by
    rw [stwE5_comap_pow]
    exact congrArg (· ^ r) (stwE5_sectionIdeal_comap c ε ψ)
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso (baseChangeSnd c ψ)
    (hJ.pow r) (hcomap ▸ hJ'.pow r)
  unfold sectionTwist
  exact ⟨e ≪≫ eqToIso (by rw [hcomap])⟩
