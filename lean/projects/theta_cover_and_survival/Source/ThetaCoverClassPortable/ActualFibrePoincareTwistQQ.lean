import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.ActualFibrePoincareTwistAlgClosedQQ
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.ActualFibrePoincareTwistQQ

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory GoodReductionJacobian AlgebraicCurve"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (q : ℚ →+* R) (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ D.P)
      (𝒲 : (pullback (pullback.snd c D.toBase) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c D.toBase s)
          (fibreModule c D.toBase s (h.poincare.L ⊗ sectionTwist c ε D.toBase r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c D.toBase s)
          (fibreModule c D.toBase s (h.poincare.L ⊗ sectionTwist c ε D.toBase r))).H0 = r + 1 - g := by
  intro k _ s 𝒲

  have hsec : rigSection c D.toBase ε ≫ pullback.snd c D.toBase = 𝟙 _ := pullback.lift_snd _ _ _
  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c D.toBase) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c D.toBase inferInstance
  have hI : (sectionIdeal c ε D.toBase).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c D.toBase ε) hsec
  have hpow : ∀ n : ℕ, ((sectionIdeal c ε D.toBase) ^ n).IsInvertible := fun n => by
    induction n with
    | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
    | succ n ih => rw [pow_succ]; exact ih.mul hI
  have hF : Scheme.Modules.IsInvertible (h.poincare.L ⊗ sectionTwist c ε D.toBase r) :=
    h.poincare.isInvertible.tensor (hpow r).isInvertible_invModule
  set F := h.poincare.L ⊗ sectionTwist c ε D.toBase r with hFdef

  let kb := AlgebraicClosure k
  obtain ⟨hH0, hH1⟩ :=
    Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
      (fibreAt c D.toBase s) 𝒲 (fibreModule c D.toBase s F) (hF.pullback _).exists_trivialization kb

  let sb : Spec (CommRingCat.of kb) ⟶ D.P := Scheme.TwoAffineOpenCover.specMap k kb ≫ s
  let φ : pullback (fibreAt c D.toBase s) (Scheme.TwoAffineOpenCover.specMap k kb) ≅
      pullback (pullback.snd c D.toBase) sb :=
    pullbackLeftPullbackSndIso (pullback.snd c D.toBase) s (Scheme.TwoAffineOpenCover.specMap k kb)
  have hφsnd : φ.inv ≫ pullback.snd (fibreAt c D.toBase s) (Scheme.TwoAffineOpenCover.specMap k kb) =
      fibreAt c D.toBase sb := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd _ _ _).symm
  have hφfst : φ.inv ≫ (pullback.fst (fibreAt c D.toBase s) (Scheme.TwoAffineOpenCover.specMap k kb) ≫
      pullback.fst (pullback.snd c D.toBase) s) = pullback.fst (pullback.snd c D.toBase) sb := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_fst _ _ _).symm

  let e : fibreModule c D.toBase sb F ≅ (Scheme.Modules.pullback φ.symm.hom).obj
      ((Scheme.Modules.pullback (pullback.fst (fibreAt c D.toBase s) (Scheme.TwoAffineOpenCover.specMap k kb))).obj
        (fibreModule c D.toBase s F)) :=
    ((Scheme.Modules.pullback φ.inv).mapIso ((Scheme.Modules.pullbackComp _ _).app F) ≪≫
      (Scheme.Modules.pullbackComp _ _).app F ≪≫ (Scheme.Modules.pullbackCongr hφfst).app F).symm
  obtain ⟨𝒱, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (fibreAt c D.toBase sb)
      (pullback.snd (fibreAt c D.toBase s) (Scheme.TwoAffineOpenCover.specMap k kb)) φ.symm hφsnd
      (𝒲.pullback (fibreAt c D.toBase s) kb) _ _ e

  obtain ⟨h1, h0⟩ :=
    P2MW.ActualFibrePoincareTwistAlgClosedQQ.solution
      R c ε q 𝔉 D h g hg r hr kb sb 𝒱
  refine ⟨?_, ?_⟩
  · haveI : Subsingleton ((𝒲.pullback (fibreAt c D.toBase s) kb).sectionsOf
        (pullback.snd (fibreAt c D.toBase s) (Scheme.TwoAffineOpenCover.specMap k kb))
        ((Scheme.Modules.pullback (pullback.fst (fibreAt c D.toBase s)
          (Scheme.TwoAffineOpenCover.specMap k kb))).obj (fibreModule c D.toBase s F))).H1 :=
      eH1.symm.toEquiv.subsingleton
    exact hH1.1 inferInstance
  · rw [← hH0, ← eH0.finrank_eq, h0]
