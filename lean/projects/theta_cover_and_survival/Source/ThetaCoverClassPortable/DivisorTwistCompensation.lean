import ThetaCoverClassPortable.RigidificationCompensation
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
namespace FourCorner.RigidificationCompensation
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c u) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c u inferInstance
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c u) (rigSection c u ε) (rigSection_snd ε u)

theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε u).pow n).isInvertible_invModule

theorem nonempty_twistModule_iso
    {g e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LU : RigidifiedLineBundle c ε u) (DγU : RelEffCartierDiv c e u)
    (D₀ : RelEffCartierDiv c g u) (D : RelEffCartierDiv c (g + e) u) (hD : D.I = D₀.I * DγU.I)
    (N : V.Modules) (hN : Scheme.Modules.IsInvertible N)
    (e₀ : D₀.lineBundle ≅ (LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) :
    Nonempty (D.twistModule c ε ≅ LU.L) := by
  have hsIr : ((sectionIdeal c ε u) ^ (g + e)).IsInvertible := (isInvertible_sectionIdeal R c ε u).pow _
  have hD₀ : D₀.I.IsInvertible := D₀.isInvertible_I
  have hDγ : DγU.I.IsInvertible := DγU.isInvertible_I

  have i1 : D.lineBundle ≅ D₀.lineBundle ⊗ DγU.lineBundle :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ≪≫ (hD₀.nonempty_mul_invModule_iso_tensor hDγ).some

  have cST : sectionTwist c ε u (g + e) ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hsIr.isInvertible_module.dual).2.some
  have cγ : DγU.lineBundle ⊗ DγU.idealModule ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hDγ.isInvertible_module.dual).2.some

  have i3 : (((LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) ⊗ DγU.lineBundle) ⊗
        ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    (α_ _ _ _) ≪≫ ((β_ _ _) ⊗ᵢ (β_ _ _)) ≪≫ (α_ _ _ _) ≪≫
      (Iso.refl _ ⊗ᵢ ((α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ
        (Scheme.Modules.tensorTensorTensorComm _ _ _ _ ≪≫ (cST ⊗ᵢ ((β_ _ _) ≪≫ cγ)) ≪≫ (λ_ _))) ≪≫ (ρ_ _)))
  have i4 : D.lineBundle ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    ((i1 ≪≫ (e₀ ⊗ᵢ Iso.refl _)) ⊗ᵢ Iso.refl _) ≪≫ i3
  have i5 : Scheme.Modules.rigidify (rigSection c u ε) (pullback.snd c u) LU.L ≅ LU.L :=
    rigidifyCounitIso _ _ LU.rigidified.some
  rw [RelEffCartierDiv.twistModule_def]
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ i4 ≪≫
    (FourCorner.RigidificationCompensation.nonempty_rigidify_pullback_tensor_iso (rigSection_snd ε u) hN LU.isInvertible).some ≪≫
    i5⟩

end FourCorner.RigidificationCompensation
