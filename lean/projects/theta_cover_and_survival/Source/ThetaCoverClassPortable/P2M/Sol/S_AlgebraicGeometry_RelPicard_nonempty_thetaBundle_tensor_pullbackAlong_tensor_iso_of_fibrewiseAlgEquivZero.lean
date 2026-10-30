import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_exists_iso_pointsSubBasepointModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicCurve GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero SmoothProperCurve.FiniteMapData RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection RigidifiedLineBundle fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso toProdSpec fstPullbackToProdSpecPullbackIso pointSubBasepointModule pointsSubBasepointModule thetaBundle IsAlgEquivZero.exists_iso_pointsSubBasepointModule nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso"
namespace ThetaLinear
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

section
variable {T : Scheme.{u}}

noncomputable def mid4 (W X Y Z : T.Modules) : (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ _ _ _ ≪≫ whiskerLeftIso W ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ X Y) Z ≪≫ α_ _ _ _) ≪≫ (α_ _ _ _).symm

noncomputable def swapRight (W X B : T.Modules) : (W ⊗ X) ⊗ B ≅ (W ⊗ B) ⊗ X :=
  α_ _ _ _ ≪≫ whiskerLeftIso W (β_ X B) ≪≫ (α_ _ _ _).symm

theorem nonempty_iso_of_tensor_iso {X Y B : T.Modules} (hB : Scheme.Modules.IsInvertible B)
    (e : X ⊗ B ≅ Y ⊗ B) : Nonempty (X ≅ Y) := by
  obtain ⟨-, ⟨d⟩⟩ := hB.dual
  exact ⟨(ρ_ X).symm ≪≫ whiskerLeftIso X d.symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso e _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso Y d ≪≫ ρ_ Y⟩

end

section
variable {k : Type u} [Field k] [Algebra ℚ k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}

noncomputable def ptsAppendIso [IsSeparated c] (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    ∀ (Ps Qs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)),
      pointsSubBasepointModule (a := c) ε (Ps ++ Qs) ≅
        pointsSubBasepointModule (a := c) ε Ps ⊗ pointsSubBasepointModule (a := c) ε Qs
  | [], Qs => (λ_ _).symm
  | P :: Ps, Qs => whiskerLeftIso (pointSubBasepointModule (a := c) P ε) (ptsAppendIso ε Ps Qs) ≪≫ (α_ _ _ _).symm

noncomputable abbrev corr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F : (pullback c t).Modules)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)) : T.Modules :=
  Ps.foldr (fun P A => (Scheme.Modules.pullback (rigSection c t P)).obj F ⊗ A) (𝟙_ T.Modules)

noncomputable def corrAppendIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F : (pullback c t).Modules) :
    ∀ (Ps Qs : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)),
      corr t F (Ps ++ Qs) ≅ corr t F Ps ⊗ corr t F Qs
  | [], Qs => (λ_ _).symm
  | P :: Ps, Qs => whiskerLeftIso ((Scheme.Modules.pullback (rigSection c t P)).obj F) (corrAppendIso t F Ps Qs) ≪≫
      (α_ _ _ _).symm

theorem isInvertible_corr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F : (pullback c t).Modules)
    (hF : Scheme.Modules.IsInvertible F) :
    ∀ (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)), Scheme.Modules.IsInvertible (corr t F Ps)
  | [] => Scheme.Modules.isInvertible_unit T
  | P :: Ps => (hF.pullback _).tensor (isInvertible_corr t F hF Ps)

end

end AlgebraicGeometry.RelPicard.ThetaLinear

open AlgebraicGeometry.RelPicard.ThetaLinear in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra ℚ k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (s : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
      (L : Type u) [Field L] [Algebra k' L] (M : CurveModel k' L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k' L) (g' : ℕ),
      (∀ D : Divisor k' L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
    (N₁ N₂ : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (hN₁ : FibrewiseAlgEquivZero N₁) (hN₂ : FibrewiseAlgEquivZero N₂)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N₁.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        thetaBundle c ε t (M.tensor (N₂.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ≅
      thetaBundle c ε t (M.tensor ((N₁.tensor N₂).pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        thetaBundle c ε t M r (r + 1 - g)) := by
  let S := Spec (CommRingCat.of k)

  have h0 : ∀ (N : RigidifiedLineBundle c ε (𝟙 S)), FibrewiseAlgEquivZero N →
      IsAlgEquivZero c ((Scheme.Modules.pullback (toProdSpec c)).obj N.L) := by
    intro N hN
    let e : C ⟶ pullback (pullback.snd c (𝟙 S)) (𝟙 S) :=
      pullback.lift (toProdSpec c) c (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
    have he : e ≫ fibreAt c (𝟙 S) (𝟙 S) = c := pullback.lift_snd _ _ _
    have hfst : e ≫ pullback.fst (pullback.snd c (𝟙 S)) (𝟙 S) = toProdSpec c := pullback.lift_fst _ _ _
    refine IsAlgEquivZero.of_iso ?_ ((hN k (𝟙 S)).pullback e he)
    exact (Scheme.Modules.pullbackComp _ _).app N.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app N.L
  have rep : ∀ (N : RigidifiedLineBundle c ε (𝟙 S)), FibrewiseAlgEquivZero N →
      ∃ Ps : List (SchemeHomOver (𝟙 S) c), Nonempty (N.L ≅ pointsSubBasepointModule (a := c) ε Ps) := by
    intro N hN
    obtain ⟨Ps, ⟨e⟩⟩ :=
      RelPicard.IsAlgEquivZero.exists_iso_pointsSubBasepointModule ε h𝔉 (N.isInvertible.pullback _) (h0 N hN)
    exact ⟨Ps, ⟨(fstPullbackToProdSpecPullbackIso c N.L).symm ≪≫ e⟩⟩
  obtain ⟨Ps₁, ⟨e₁⟩⟩ := rep N₁ hN₁
  obtain ⟨Ps₂, ⟨e₂⟩⟩ := rep N₂ hN₂
  have e₁₂ : (N₁.tensor N₂).L ≅ pointsSubBasepointModule (a := c) ε (Ps₁ ++ Ps₂) :=
    (e₁ ⊗ᵢ e₂) ≪≫ (ptsAppendIso ε Ps₁ Ps₂).symm

  obtain ⟨φ₁⟩ := RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso k c ε h𝔉 g hg
    M hM Ps₁ N₁ hN₁ e₁ r hr
  obtain ⟨φ₂⟩ := RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso k c ε h𝔉 g hg
    M hM Ps₂ N₂ hN₂ e₂ r hr
  obtain ⟨φ₁₂⟩ := RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso k c ε h𝔉 g hg
    M hM (Ps₁ ++ Ps₂) (N₁.tensor N₂) (hN₁.tensor hN₂) e₁₂ r hr

  have hB : Scheme.Modules.IsInvertible (corr t M.L Ps₁ ⊗ corr t M.L Ps₂) :=
    (isInvertible_corr t M.L M.isInvertible Ps₁).tensor (isInvertible_corr t M.L M.isInvertible Ps₂)
  refine nonempty_iso_of_tensor_iso hB ?_
  refine mid4 _ _ _ _ ≪≫ (φ₁ ⊗ᵢ φ₂) ≪≫ ?_
  refine (whiskerRightIso (whiskerLeftIso _ (corrAppendIso t M.L Ps₁ Ps₂).symm ≪≫ φ₁₂) _).symm ≪≫ ?_
  exact (swapRight _ _ _).symm
