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
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesDet
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback
import ThetaCoverClassPortable.ActualRigidifiedFibreTwistQQ
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionIdeal_pow_module_iso
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve AlgebraicCurve GoodReductionJacobian"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral LocallyOfFiniteType Spec Scheme IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv graphOver RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I Scheme.IdealSheafData.IsInvertible SmoothProperCurve.FiniteMapData Scheme.Modules.dualMapIso Scheme.Modules.exteriorPower Scheme.Modules.det RelPicard.nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback  RelPicard.nonempty_pullback_sectionTwist_iso Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.Modules.IsInvertible.dual_tensor Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso RelPicard.nonempty_pullback_sectionIdeal_pow_module_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso pointSubBasepointModule sectionIdeal sectionTwist thetaBundle fibreModule nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback  nonempty_pullback_sectionTwist_iso RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit isLocallyFreeOfRank_pushforward_of_forall_fibre forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso nonempty_pullback_sectionIdeal_pow_module_iso"
namespace ThetaStep
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k] [Algebra ℚ k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}

noncomputable def ofField (L : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules) (hL : Scheme.Modules.IsInvertible L) :
    RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))) where
  L := L
  isInvertible := hL
  rigidified := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hL.pullback _)

noncomputable def swapR {X : Scheme.{u}} (A B D : X.Modules) : (A ⊗ B) ⊗ D ≅ (A ⊗ D) ⊗ B :=
  α_ _ _ _ ≪≫ whiskerLeftIso A (β_ B D) ≪≫ (α_ _ _ _).symm

theorem isInvertible_sectionIdeal [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) :
    (sectionIdeal c Q t).IsInvertible := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t Q) (pullback.lift_snd _ _ _)

theorem rigSection_eq_graphOver (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    rigSection c (𝟙 (Spec (CommRingCat.of k))) Q = graphOver c Q.1 Q.2 := by
  apply pullback.hom_ext
  · simp [rigSection, graphOver]
  · simp [rigSection, graphOver]

theorem sectionIdeal_one_eq [IsSeparated c] (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    (sectionIdeal c Q (𝟙 (Spec (CommRingCat.of k)))) ^ 1 = (RelEffCartierDiv.ofPoint c Q.1 Q.2).I := by
  rw [pow_one, RelEffCartierDiv.ofPoint_I, sectionIdeal, rigSection_eq_graphOver]

end AlgebraicGeometry.RelPicard.ThetaStep

open AlgebraicGeometry.RelPicard.ThetaStep in
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
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k)))) (hN : FibrewiseAlgEquivZero N)
    (eN : N.L ≅ pointSubBasepointModule (a := c) P ε)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        (Scheme.Modules.pullback (rigSection c t P)).obj M.L ≅
      thetaBundle c ε t M r (r + 1 - g)) := by

  let S := Spec (CommRingCat.of k)
  let tT : SchemeHomOver t (𝟙 S) := ⟨t, Category.comp_id t⟩
  let π := pullback.snd c t
  let F : (pullback c t).Modules := M.L
  let Iε : (pullback c t).IdealSheafData := sectionIdeal c ε t
  let IP : (pullback c t).IdealSheafData := sectionIdeal c P t
  let Orε : (pullback c t).Modules := sectionTwist c ε t r
  let OP : (pullback c t).Modules := sectionTwist c P t 1
  let G : (pullback c t).Modules := (F ⊗ Orε) ⊗ OP
  let NT := N.pullbackAlong tT

  have hIε : Iε.IsInvertible := isInvertible_sectionIdeal ε t
  have hIP : IP.IsInvertible := isInvertible_sectionIdeal P t
  have hIεr : (Iε ^ r).IsInvertible := hIε.pow r
  have hF : Scheme.Modules.IsInvertible F := M.isInvertible
  have hOrε : Scheme.Modules.IsInvertible Orε := hIεr.isInvertible_invModule
  have hOP : Scheme.Modules.IsInvertible OP := (hIP.pow 1).isInvertible_invModule
  have hG : Scheme.Modules.IsInvertible G := (hF.tensor hOrε).tensor hOP

  have pairP : OP ⊗ IP.module ≅ 𝟙_ _ :=
    whiskerRightIso (eqToIso (by rw [pow_one] : (IP ^ 1).invModule = IP.invModule)) _ ≪≫
      (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hIP).some
  have pairε : Iε.invModule ⊗ Iε.module ≅ 𝟙_ _ :=
    (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hIε).some

  have ea : G ⊗ IP.module ≅ F ⊗ Orε := α_ _ _ _ ≪≫ whiskerLeftIso _ pairP ≪≫ ρ_ _

  obtain ⟨bcP⟩ := RelPicard.nonempty_pullback_sectionTwist_iso k c P tT 1
  obtain ⟨bcε⟩ := RelPicard.nonempty_pullback_sectionIdeal_pow_module_iso k c ε tT 1
  have eNT : NT.L ≅ OP ⊗ Iε.module :=
    (Scheme.Modules.pullback _).mapIso eN ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (((Scheme.Modules.pullback _).mapIso (eqToIso
          (congrArg Scheme.IdealSheafData.invModule (sectionIdeal_one_eq (c := c) P).symm)) ≪≫ bcP) ⊗ᵢ
        ((Scheme.Modules.pullback _).mapIso (eqToIso
          (congrArg Scheme.IdealSheafData.module (sectionIdeal_one_eq (c := c) ε).symm)) ≪≫ bcε ≪≫
          eqToIso (by rw [pow_one])))
  have eb : G ⊗ Iε.module ≅ (M.tensor NT).L ⊗ Orε :=
    α_ _ _ _ ≪≫ swapR _ _ _ ≪≫ whiskerRightIso (whiskerLeftIso F eNT.symm) _

  have eSucc : sectionTwist c ε t (r + 1) ≅ Orε ⊗ Iε.invModule :=
    eqToIso (by rw [pow_succ] : (Iε ^ (r + 1)).invModule = (Iε ^ r * Iε).invModule) ≪≫
      (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hIεr hIε).some
  have ec : G ≅ (M.tensor NT).L ⊗ sectionTwist c ε t (r + 1) :=
    (ρ_ G).symm ≪≫ whiskerLeftIso G (pairε.symm ≪≫ β_ _ _) ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso eb _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ eSucc.symm

  have hMNT : FibrewiseAlgEquivZero (M.tensor NT) := hM.tensor (hN.pullback tT)
  obtain ⟨𝔉0,_⟩ := h𝔉 0
  have hfibM := P2MW.ActualRigidifiedFibreTwistQQ.solution
    k c ε (algebraMap ℚ k) 𝔉0 g hg M hM r hr
  have hfibMN := P2MW.ActualRigidifiedFibreTwistQQ.solution
    k c ε (algebraMap ℚ k) 𝔉0 g hg (M.tensor NT) hMNT r hr
  have hfibMN1 := P2MW.ActualRigidifiedFibreTwistQQ.solution
    k c ε (algebraMap ℚ k) 𝔉0 g hg (M.tensor NT) hMNT (r + 1) (by omega)
  have h_a := RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso c t ea.symm (r + 1 - g) hfibM
  have h_b := RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso c t eb.symm (r + 1 - g) hfibMN
  have h_c : ∀ (k' : Type u) [Field k'] (s : Spec (CommRingCat.of k') ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s G)).H1 ∧
        Module.finrank k' (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s G)).H0 = r + 1 - g + 1 := by
    have h := RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso c t ec.symm (r + 1 + 1 - g) hfibMN1
    intro k' _ s 𝒲
    obtain ⟨h1, h0⟩ := h k' s 𝒲
    exact ⟨h1, by omega⟩

  obtain ⟨dP⟩ := RelPicard.nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback k c ε h𝔉 t
    (rigSection c t P) (pullback.lift_snd _ _ _) G hG (r + 1 - g) h_a h_c
  obtain ⟨dε⟩ := RelPicard.nonempty_det_pushforward_iso_det_pushforward_tensor_idealOfSection_tensor_pullback k c ε h𝔉 t
    (rigSection c t ε) (pullback.lift_snd _ _ _) G hG (r + 1 - g) h_b h_c

  have detA : Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (G ⊗ IP.module)) ≅
      Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (F ⊗ Orε)) :=
    (Scheme.Modules.exteriorPower T (r + 1 - g)).mapIso ((Scheme.Modules.pushforward π).mapIso ea)
  have detB : Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (G ⊗ Iε.module)) ≅
      Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj ((M.tensor NT).L ⊗ Orε)) :=
    (Scheme.Modules.exteriorPower T (r + 1 - g)).mapIso ((Scheme.Modules.pushforward π).mapIso eb)

  let W : (pullback c (𝟙 S)).Modules := sectionTwist c ε (𝟙 S) r ⊗ sectionTwist c P (𝟙 S) 1
  have hW : Scheme.Modules.IsInvertible W :=
    ((isInvertible_sectionIdeal ε (𝟙 S)).pow r).isInvertible_invModule.tensor
      ((isInvertible_sectionIdeal P (𝟙 S)).pow 1).isInvertible_invModule
  let NW : RigidifiedLineBundle c ε (𝟙 S) := ofField W hW
  obtain ⟨bcεr⟩ := RelPicard.nonempty_pullback_sectionTwist_iso k c ε tT r
  have eW : Orε ⊗ OP ≅ (NW.pullbackAlong tT).L :=
    (Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (bcεr ⊗ᵢ bcP)).symm
  have eG : G ≅ F ⊗ (NW.pullbackAlong tT).L := α_ _ _ _ ≪≫ whiskerLeftIso F eW
  obtain ⟨invP⟩ := RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit NW P t
  obtain ⟨invε⟩ := RigidifiedLineBundle.nonempty_pullback_rigSection_pullbackAlong_iso_tensorUnit NW ε t
  have pG : (Scheme.Modules.pullback (rigSection c t P)).obj G ≅ (Scheme.Modules.pullback (rigSection c t P)).obj F :=
    (Scheme.Modules.pullback _).mapIso eG ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      whiskerLeftIso _ invP ≪≫ ρ_ _
  have εG : (Scheme.Modules.pullback (rigSection c t ε)).obj G ≅ 𝟙_ _ :=
    (Scheme.Modules.pullback _).mapIso eG ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      (M.rigidified.some ⊗ᵢ invε) ≪≫ λ_ _

  have eD : Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj ((M.tensor NT).L ⊗ Orε)) ≅
      Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (F ⊗ Orε)) ⊗
        (Scheme.Modules.pullback (rigSection c t P)).obj F :=
    ((dε ≪≫ (detB ⊗ᵢ εG) ≪≫ ρ_ _).symm) ≪≫ dP ≪≫ (detA ⊗ᵢ pG)

  have hDM : Scheme.Modules.IsInvertible
      (Scheme.Modules.det (r + 1 - g) ((Scheme.Modules.pushforward π).obj (F ⊗ Orε))) :=
    Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank
      (RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre k c ε h𝔉 t (F ⊗ Orε) (hF.tensor hOrε) (r + 1 - g) hfibM)
  have hA : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (rigSection c t P)).obj F) := hF.pullback _
  obtain ⟨dualT⟩ := Scheme.Modules.IsInvertible.dual_tensor hDM hA
  obtain ⟨-, ⟨pairA⟩⟩ := hA.dual
  refine ⟨whiskerRightIso (Scheme.Modules.dualMapIso eD ≪≫ dualT) _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (β_ _ _ ≪≫ pairA) ≪≫ ρ_ _⟩
