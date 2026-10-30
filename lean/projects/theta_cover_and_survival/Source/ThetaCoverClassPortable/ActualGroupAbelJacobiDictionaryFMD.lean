import Mathlib.AlgebraicGeometry.Geometrically.Connected
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver

import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat
import ThetaCoverClassPortable.ActualPic0DictionaryFMD
import ThetaCoverClassPortable.FiniteMapDataBaseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.ActualGroupAbelJacobiDictionaryFMD

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.ActualGroupAbelJacobiDictionaryFMD.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.ActualGroupAbelJacobiDictionaryFMD.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.SmoothProperCurve"

universe u v

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.range_fiberι Spec Spec.map Scheme Smooth IsSeparated Scheme.Modules GeometricallyConnected geometrically Scheme.IdealSheafData Scheme.Modules.pullbackTensorObjIso Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv graphOver graphOver_fst graphOver_snd RelEffCartierDiv.ofPoint graphOver_fst_assoc RelEffCartierDiv.isInvertible_I Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso RelPicard.exists_abelJacobi_of_representsRelSubPic RelPicard.baseChange_points_mul_poincare_compat  RelPicard.exists_representsRelSubPic_baseChange"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RepresentsRelSubPic algEquivZeroCut algEquivZeroGroupCut BaseChange.κ BaseChange.κ_hom_snd BaseChange.κ_hom_fst pointsSubBasepointModule pointsSubBasepointModule_nil pointsSubBasepointModule_cons exists_abelJacobi_of_representsRelSubPic baseChange_points_mul_poincare_compat  exists_representsRelSubPic_baseChange"
namespace DictGlue
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem essFiniteType_of_curveModel {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) : Algebra.EssFiniteType K L := by
  letI := M.functionFieldAlgebra
  haveI : Algebra.EssFiniteType K M.C.functionField :=
    AlgebraicCurve.essFiniteType_functionField M.toBase
  exact Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom M.ffAlgEquiv.symm.surjective

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem isConnected_fibre_of_geometricallyConnected {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (hgc : GeometricallyConnected f)
    (z : Spec (CommRingCat.of R) ⟶ A) (hz : z ≫ f = 𝟙 _) :
    ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s}) := by
  intro s
  haveI := hgc
  have h := isConnected_range (f.fiberι s).continuous
  rwa [Scheme.Hom.range_fiberι] at h

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem nonempty_pullback_κ_inv_pointsSubBasepointModule_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (K : Type u) [Field K] [Algebra R K]
    (xK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K)) :
    Nonempty ((Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
        (pointsSubBasepointModule (a := baseChange R c K) (sectionBaseChange K ε) [xK]) ≅
      (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K))
          ((Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
            ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ specMap R K) xK.2).trans (Category.id_comp _)))))).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (specMap R K ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) := by

  have hx : (xK.1 ≫ pullback.fst c (specMap R K)) ≫ c =
      𝟙 (Spec (CommRingCat.of K)) ≫ specMap R K :=
    (Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ specMap R K) xK.2)))
  have hε : (specMap R K ≫ ε.1) ≫ c = 𝟙 (Spec (CommRingCat.of K)) ≫ specMap R K :=
    (Category.assoc _ _ _).trans (((congrArg (specMap R K ≫ ·) ε.2).trans (Category.comp_id _)).trans
      (Category.id_comp _).symm)

  have hpx : graphOver c (xK.1 ≫ pullback.fst c (specMap R K)) hx ≫
      (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv =
        graphOver (baseChange R c K) xK.1 xK.2 := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]
  have hpε : graphOver c (specMap R K ≫ ε.1) hε ≫
      (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv =
        graphOver (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2 := by
    rw [Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, BaseChange.κ_hom_fst, graphOver_fst_assoc,
        sectionBaseChange_coe_fst]
    · rw [graphOver_snd, Category.assoc, BaseChange.κ_hom_snd, graphOver_snd]

  obtain ⟨ex⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv
    (graphOver (baseChange R c K) xK.1 xK.2) (graphOver c (xK.1 ≫ pullback.fst c (specMap R K)) hx) hpx
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint (baseChange R c K) xK.1 xK.2))
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K)) hx))
    1).1
  obtain ⟨eε⟩ := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv
    (graphOver (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2)
    (graphOver c (specMap R K ≫ ε.1) hε) hpε
    (RelEffCartierDiv.isInvertible_I
      (RelEffCartierDiv.ofPoint (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2))
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1) hε))
    1).2

  have ex' : (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
      (RelEffCartierDiv.ofPoint (baseChange R c K) xK.1 xK.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (xK.1 ≫ pullback.fst c (specMap R K)) hx).lineBundle :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _).symm)) ≪≫ ex ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.invModule (pow_one _))
  have eε' : (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 (Spec (CommRingCat.of K)))).inv).obj
      (RelEffCartierDiv.ofPoint (baseChange R c K) (sectionBaseChange K ε).1 (sectionBaseChange K ε).2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (specMap R K ≫ ε.1) hε).idealModule :=
    (Scheme.Modules.pullback _).mapIso
        (eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _).symm)) ≪≫ eε ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))

  rw [pointsSubBasepointModule_cons, pointsSubBasepointModule_nil]
  exact ⟨(Scheme.Modules.pullback _).mapIso (ρ_ _) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    tensorIso ex' eε'⟩

end AlgebraicGeometry.RelPicard.DictGlue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase) :
    ∃ (L : RelativeGroupLaw R D.toBase) (aj : SchemeHomOver c D.toBase),
      AbelianSchemePropertyBundle R D.toBase ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        L.mul t x y = L.mul t y x) ∧
      (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = D.zeroSection ∧
      ε.1 ≫ aj.1 = D.zeroSection ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : R →+* K)
        (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) D.toBase,
          (∀ x y : Pic0 K F,
            pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) =
              Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) =
                Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 =
                x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1 := by

  let hG : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D := h
  haveI : IsSeparated c := inferInstance
  obtain ⟨aj, hajε, hajP⟩ := AlgebraicGeometry.RelPicard.exists_abelJacobi_of_representsRelSubPic R c ε D h
  refine ⟨hG.relativeGroupLaw, aj, ?_, ?_, hG.relativeGroupLaw_one, ?_, ?_⟩
  ·
    exact ⟨hsm, hpr, DictGlue.isConnected_fibre_of_geometricallyConnected D.toBase hgc D.zeroSection D.zeroSection_toBase,
      ⟨hG.relativeGroupLaw⟩⟩
  ·
    intro T t x y
    exact hG.relativeGroupLaw_isCommutative t x y
  ·
    exact hajε
  ·
    intro K _ _ i F _ _ _ M e _ he
    letI : Algebra R K := i.toAlgebra
    haveI : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M

    obtain ⟨h', hP'⟩ := AlgebraicGeometry.RelPicard.exists_representsRelSubPic_baseChange R c ε D h K
    obtain ⟨Θ, hΘ1, hΘmul, hΘP⟩ := AlgebraicGeometry.RelPicard.baseChange_points_mul_poincare_compat R c ε D h K h' hP'

    let eI : M.C ≅ pullback c (specMap R K) := asIso e
    have heI : eI.hom ≫ baseChange R c K = M.toBase := he
    let εK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K) := sectionBaseChange K ε
    let ε'ₘ : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
      ⟨εK.1 ≫ inv e, by rw [Category.assoc, ← heI]; show εK.1 ≫ inv e ≫ e ≫ _ = _; rw [IsIso.inv_hom_id_assoc]; exact εK.2⟩
    have hε'ₘ : ε'ₘ.1 ≫ eI.hom = εK.1 := by show (εK.1 ≫ inv e) ≫ e = εK.1; rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    obtain ⟨pts, hadd, hAJ, -⟩ :=
      P2MW.ActualPic0DictionaryFMD.solution K (baseChange R c K) εK (𝔉.baseChange K)
        (D.baseChange K) h' M eI heI ε'ₘ hε'ₘ
    refine ⟨pts.trans Θ, fun x y => ?_, fun x s hs => ?_⟩
    · show Θ (pts (x + y)) = _
      rw [hadd, hΘmul]
      rfl
    ·
      have hsK : s.1 ≫ e = εK.1 := by
        apply pullback.hom_ext
        · rw [Category.assoc]
          exact hs.trans (sectionBaseChange_coe_fst (R := R) K ε).symm
        · rw [Category.assoc]
          change s.1 ≫ eI.hom ≫ baseChange R c K = εK.1 ≫ pullback.snd _ _
          rw [heI, s.2]
          exact (sectionBaseChange_coe_snd (R := R) K ε).symm
      have hsε : s = ε'ₘ := by
        apply Subtype.ext
        show s.1 = εK.1 ≫ inv e
        rw [← hsK, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      subst hsε
      have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
      have hDv : Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace ε'ₘ) 1 ∈
          Divisor.degZero (K := K) (F := F) := by
        rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
        simp
      refine ⟨⟨Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace ε'ₘ) 1, hDv⟩, rfl, ?_⟩
      ·
        obtain ⟨iAJ⟩ := hAJ [x] ⟨_, hDv⟩ (by
          show Finsupp.single (M.pointEquivPlace x) (1 : ℤ) - Finsupp.single (M.pointEquivPlace ε'ₘ) 1 = _
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_cons,
            List.length_nil, zero_add, Nat.cast_one, one_smul])

        let xK : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (baseChange R c K) :=
          ⟨x.1 ≫ eI.hom, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) heI).trans x.2)⟩
        let xR : SchemeHomOver (specMap R K) c :=
          ⟨xK.1 ≫ pullback.fst c (specMap R K),
            (Category.assoc _ _ _).trans ((congrArg (xK.1 ≫ ·) pullback.condition).trans
              ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ specMap R K) xK.2).trans (Category.id_comp _))))⟩
        obtain ⟨iR⟩ := hajP K (specMap R K) xR
        obtain ⟨iΘ⟩ := hΘP (pts (Pic0.mk ⟨_, hDv⟩))

        have key : Θ (pts (Pic0.mk ⟨Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace ε'ₘ) 1, hDv⟩)) =
            ⟨xR.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (xR.1 ≫ ·) aj.2).trans xR.2)⟩ := by
          apply h.ext_of_iso (specMap R K)
          obtain ⟨iM⟩ := DictGlue.nonempty_pullback_κ_inv_pointsSubBasepointModule_iso R c ε K xK
          exact ⟨iΘ ≪≫ (Scheme.Modules.pullback (BaseChange.κ c K (𝟙 _)).inv).mapIso iAJ ≪≫ iM ≪≫ iR.symm⟩
        show (Θ (pts (Pic0.mk ⟨_, hDv⟩))).1 = _
        rw [key]
        show ((x.1 ≫ e) ≫ pullback.fst c (specMap R K)) ≫ aj.1 = _
        simp only [Category.assoc] <;> rfl
