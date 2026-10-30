import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_RelCartier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.ActualLargeDegreeTwistQQ
import ThetaCoverClassPortable.FiniteMapDataBaseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.ActualFibrePoincareTwistAlgClosedQQ

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory GoodReductionJacobian AlgebraicCurve AlgebraicGeometry.SmoothProperCurve"

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
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ D.P)
      (𝒲 : (pullback (pullback.snd c D.toBase) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c D.toBase s)
          (fibreModule c D.toBase s (h.poincare.L ⊗ sectionTwist c ε D.toBase r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c D.toBase s)
          (fibreModule c D.toBase s (h.poincare.L ⊗ sectionTwist c ε D.toBase r))).H0 = r + 1 - g := by
  intro k _ _ s 𝒲

  let σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := s ≫ D.toBase
  obtain ⟨a,ha⟩ := Spec.map_surjective σ
  letI : Algebra R k := a.hom.toAlgebra
  letI : Algebra ℚ k := ((algebraMap R k).comp q).toAlgebra
  have hs : specMap R k = σ := ha
  have F : SmoothProperCurve.FiniteMapData (pullback.snd c σ)
      (⟨rigSection c σ ε,pullback.lift_snd _ _ _⟩ : SchemeHomOver (𝟙 _) (pullback.snd c σ)) := by
    rw [←hs]
    exact 𝔉.baseChange k
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : IsIntegral (pullback c σ) := GeometricallyIntegral.geometrically_isIntegral
    (f:=c) σ (pullback.fst c σ) (pullback.snd c σ) (.of_hasPullback _ _)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c σ) := MorphismProperty.pullback_snd _ _ inferInstance
  let ψ : SchemeHomOver σ D.toBase := ⟨s, rfl⟩
  let κ : pullback (pullback.snd c D.toBase) s ≅ pullback c σ := pullbackLeftPullbackSndIso c D.toBase s
  have hκsnd : κ.inv ≫ fibreAt c D.toBase s = pullback.snd c σ := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd c D.toBase s).symm
  have hκbcs : κ.inv ≫ pullback.fst (pullback.snd c D.toBase) s = baseChangeSnd c ψ := by
    rw [Iso.inv_comp_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, baseChangeSnd, pullback.lift_fst, Category.comp_id]
      exact (pullbackLeftPullbackSndIso_hom_fst c D.toBase s).symm
    · rw [Category.assoc, baseChangeSnd, pullback.lift_snd, pullback.condition, ← Category.assoc,
        pullbackLeftPullbackSndIso_hom_snd]

  obtain ⟨iTw⟩ := RelPicard.nonempty_pullback_sectionTwist_iso R c ε ψ r
  let e : (h.poincare.pullbackAlong ψ).L ⊗ (((rigSection c σ ε).ker) ^ r).invModule ≅
      (Scheme.Modules.pullback κ.symm.hom).obj
        (fibreModule c D.toBase s (h.poincare.L ⊗ sectionTwist c ε D.toBase r)) :=
    ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hκbcs).app _ ≪≫
      Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) h.poincare.L (sectionTwist c ε D.toBase r) ≪≫
      whiskerLeftIso _ iTw).symm
  obtain ⟨𝒱, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (pullback.snd c σ) (fibreAt c D.toBase s)
      κ.symm hκsnd 𝒲 _ _ e

  have hmem : FibrewiseAlgEquivZero h.poincare := h.poincare_mem
  have h0 : IsAlgEquivZero (pullback.snd c σ) (h.poincare.pullbackAlong ψ).L :=
    IsAlgEquivZero.of_iso ((Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hκbcs).app _)
      ((hmem k s).pullback κ.inv hκsnd)

  obtain ⟨h1, h0'⟩ :=
    FourCorner.ActualPicardProperties.largeDegreeTwist_of_RR_genus_QQ
      (pullback.snd c σ) ⟨rigSection c σ ε,pullback.lift_snd _ _ _⟩ F g (fun L _ _ M e' he Kc g' hRR => hg k σ L M e' he Kc g' hRR)
      (h.poincare.pullbackAlong ψ).L
      (h.poincare.pullbackAlong ψ).isInvertible h0 r hr 𝒱
  refine ⟨?_, ?_⟩
  · haveI := h1
    exact eH1.symm.toEquiv.subsingleton
  · rw [← eH0.finrank_eq]
    exact h0'
