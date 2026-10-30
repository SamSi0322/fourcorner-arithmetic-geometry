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
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_iso_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicCurve GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsSeparated Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv RelEffCartierDiv.isInvertible_I SmoothProperCurve.FiniteMapData RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso RelPicard.nonempty_thetaBundle_iso_of_iso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection RigidifiedLineBundle FibrewiseAlgEquivZero pointSubBasepointModule pointsSubBasepointModule thetaBundle nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit nonempty_thetaBundle_iso_of_iso RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule"
namespace ThetaPoints
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k] [Algebra ℚ k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}

noncomputable def ofField (L : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules) (hL : Scheme.Modules.IsInvertible L) :
    RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))) where
  L := L
  isInvertible := hL
  rigidified := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hL.pullback _)

theorem isInvertible_pointSubBasepointModule [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    Scheme.Modules.IsInvertible (pointSubBasepointModule (a := c) P ε) :=
  (RelEffCartierDiv.isInvertible_I _).isInvertible_invModule.tensor (RelEffCartierDiv.isInvertible_I _).isInvertible_module

theorem isInvertible_pointsSubBasepointModule [IsSeparated c] [SmoothOfRelativeDimension 1 c] :
    ∀ (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)),
      Scheme.Modules.IsInvertible (pointsSubBasepointModule (a := c) ε Ps)
  | [] => Scheme.Modules.isInvertible_unit _
  | P :: Ps => (isInvertible_pointSubBasepointModule P).tensor (isInvertible_pointsSubBasepointModule Ps)

noncomputable abbrev corr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F : (pullback c t).Modules)
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)) : T.Modules :=
  Ps.foldr (fun P A => (Scheme.Modules.pullback (rigSection c t P)).obj F ⊗ A) (𝟙_ T.Modules)

noncomputable def corrCongr {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (F F' : (pullback c t).Modules)
    (h : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c,
      (Scheme.Modules.pullback (rigSection c t P)).obj F ≅ (Scheme.Modules.pullback (rigSection c t P)).obj F') :
    ∀ (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)), corr t F Ps ≅ corr t F' Ps
  | [] => Iso.refl _
  | P :: Ps => h P ⊗ᵢ corrCongr t F F' h Ps

noncomputable def rot {T : Scheme.{u}} (X A B : T.Modules) : X ⊗ (A ⊗ B) ≅ (X ⊗ B) ⊗ A :=
  whiskerLeftIso X (β_ A B) ≪≫ (α_ _ _ _).symm

end AlgebraicGeometry.RelPicard.ThetaPoints

open AlgebraicGeometry.RelPicard.ThetaPoints in
theorem solution
    (k : Type u) [Field k] [Algebra ℚ k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
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
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c))
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k)))) (hN : FibrewiseAlgEquivZero N)
    (eN : N.L ≅ pointsSubBasepointModule (a := c) ε Ps)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        Ps.foldr (fun P A => (Scheme.Modules.pullback (rigSection c t P)).obj M.L ⊗ A) (𝟙_ T.Modules) ≅
      thetaBundle c ε t M r (r + 1 - g)) := by
  let S := Spec (CommRingCat.of k)
  let tT : SchemeHomOver t (𝟙 S) := ⟨t, Category.comp_id t⟩

  suffices key : ∀ (Qs : List (SchemeHomOver (𝟙 S) c)) (M : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero M →
      ∀ (N : RigidifiedLineBundle c ε (𝟙 S)), FibrewiseAlgEquivZero N →
        (N.L ≅ pointsSubBasepointModule (a := c) ε Qs) →
        Nonempty (thetaBundle c ε t (M.tensor (N.pullbackAlong tT)) r (r + 1 - g) ⊗ corr t M.L Qs ≅
          thetaBundle c ε t M r (r + 1 - g)) from
    key Ps M hM N hN eN
  intro Qs
  induction Qs with
  | nil =>
    intro M hM N hN eN

    have e : (M.tensor (N.pullbackAlong tT)).L ≅ M.L :=
      whiskerLeftIso M.L ((Scheme.Modules.pullback _).mapIso eN ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫ ρ_ M.L
    obtain ⟨θ⟩ := RelPicard.nonempty_thetaBundle_iso_of_iso c ε t _ _ e r (r + 1 - g)
    exact ⟨ρ_ _ ≪≫ θ⟩
  | cons P Qs ih =>
    intro M hM N hN eN

    let NP : RigidifiedLineBundle c ε (𝟙 S) := ofField (pointSubBasepointModule (a := c) P ε)
      (isInvertible_pointSubBasepointModule P)
    let N' : RigidifiedLineBundle c ε (𝟙 S) := ofField (pointsSubBasepointModule (a := c) ε Qs)
      (isInvertible_pointsSubBasepointModule Qs)
    have hNP : FibrewiseAlgEquivZero NP :=
      RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule NP [P] (ρ_ _).symm
    have hN' : FibrewiseAlgEquivZero N' :=
      RigidifiedLineBundle.fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule N' Qs (Iso.refl _)
    let M₁ : RigidifiedLineBundle c ε t := M.tensor (NP.pullbackAlong tT)
    have hM₁ : FibrewiseAlgEquivZero M₁ := hM.tensor (hNP.pullback tT)

    obtain ⟨σ⟩ := RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso k c ε h𝔉 g hg M hM P NP
      hNP (Iso.refl _) r hr

    obtain ⟨τ⟩ := ih M₁ hM₁ N' hN' (Iso.refl _)

    have e : (M.tensor (N.pullbackAlong tT)).L ≅ (M₁.tensor (N'.pullbackAlong tT)).L :=
      whiskerLeftIso M.L ((Scheme.Modules.pullback _).mapIso eN ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _) ≪≫
        (α_ _ _ _).symm
    obtain ⟨θ⟩ := RelPicard.nonempty_thetaBundle_iso_of_iso c ε t _ _ e r (r + 1 - g)

    have cc : corr t M₁.L Qs ≅ corr t M.L Qs := by
      refine (corrCongr t M.L M₁.L (fun Q => ?_) Qs).symm
      exact (ρ_ _).symm ≪≫ whiskerLeftIso _
        (RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit NP Q t).some.symm ≪≫
        (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

    exact ⟨(θ ⊗ᵢ whiskerLeftIso _ cc.symm) ≪≫ rot _ _ _ ≪≫ (τ ⊗ᵢ Iso.refl _) ≪≫ σ⟩
