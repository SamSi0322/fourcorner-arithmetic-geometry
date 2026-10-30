import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import ThetaCoverClassPortable.Definitions.Def_CategoryTheory_OverTotalPresheaf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGlue
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_AffineLimit
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_AffineLimit_homIsLFP_of_locallyOfFinitePresentation
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_AffineLimit_presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
import ThetaCoverClassPortable.ActualCutLFP
import ThetaCoverClassPortable.ActualLFPInjectivity
import ThetaCoverClassPortable.ActualSingleChartConstruction
import ThetaCoverClassPortable.ActualChartEulerOfSections
import ThetaCoverClassPortable.ActualChartCoverage
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ThetaCoverClassPortable.P2M.Util
namespace FourCorner.ActualPicardAtlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve~genus AlgebraicGeometry.AffineLimit"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (n g r : ℕ) (hgr : 2 * g < r)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hγ : HasChartSections c γ)
    (hUniv : ∀d:ℕ,∃(Y:Scheme.{u})(y:Y⟶Spec (.of R))(D:RelEffCartierDiv c d y),D.IsUniversal)
    (hSheaf : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (.of R)))
      (relSubPicPresheaf c ε (algEquivZeroCut c ε))) :
    ∃ (X : ULift.{u} (Fin n) → Scheme.{u})
      (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      (∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i)) ∧
        Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) := by

  obtain ⟨F,-⟩ := h𝔉 0
  obtain ⟨Y,y,Duniv,hU⟩ := hUniv g

  have hD : ∀ i : Fin n, ∃ D : RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))),
      D.I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2) := fun i =>
    AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph (fun j => (γ i j).1) (fun j => (γ i j).2)
  choose Dγ hDγ using hD
  have hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1 :=
    fun i k _ _ x 𝒲 =>
      FourCorner.ActualChartEulerOfSections.chart_euler c ε F hgr γ hγ (Dγ i) x 𝒲

  have hch := fun i : ULift.{u} (Fin n) =>
    FourCorner.ActualSingleChartConstruction.solution
      R c ε h𝔉 g (r - g) r (by omega) (Dγ i.down) (hχ i.down) Y y Duniv hU
  choose X f hlft hchart using hch
  refine ⟨X, f, ?_⟩
  have hG : Presieve.IsSheaf Scheme.zariskiTopology (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal :=
    (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal_isSheaf _
      hSheaf
  refine AlgebraicGeometry.AffineLimit.presheafULift_isOpenImmersion_and_isLocallySurjective_of_locallyOfFiniteType
    R _ hG
    (FourCorner.ActualCutLFP.finite_stage_injective_and_surjective R c ε F).2
    (FourCorner.ActualCutLFP.finite_stage_injective_and_surjective R c ε F).1
    X f (fun i => by haveI := hlft i; exact AlgebraicGeometry.AffineLimit.homIsLFP_of_locallyOfFinitePresentation R _) ?_
  intro T x hx
  have hc := fun i => hchart i x hx
  choose U φ hU using hc
  refine ⟨U, φ, ?_, fun i => ⟨(hU i).2.1, (hU i).2.2⟩⟩

  rw [eq_top_iff]
  rintro p -
  let t := (uliftYonedaEquiv x).1
  haveI : LocallyOfFiniteType t := hx
  let L : RigidifiedLineBundle c ε t := Quotient.out (uliftYonedaEquiv x).2.1
  have hLx : Quotient.mk _ L = (uliftYonedaEquiv x).2.1 := Quotient.out_eq _
  have hL : FibrewiseAlgEquivZero L := by
    have h2 := (uliftYonedaEquiv x).2.2
    rw [← hLx] at h2
    exact h2
  obtain ⟨i, hi⟩ := FourCorner.ActualChartCovering.solution R c ε F n g r hgr γ hγ Dγ hDγ t L hL
    (T.residueField p) (T.fromSpecResidueField p)
  have hmem : Set.range ⇑(T.fromSpecResidueField p) ⊆ (U ⟨i⟩ : Set T) :=
    ((hU ⟨i⟩).1 L hLx (T.residueField p) (T.fromSpecResidueField p)).mpr hi
  have hp : p ∈ U ⟨i⟩ := hmem ⟨IsLocalRing.closedPoint _, by exact T.fromSpecResidueField_apply p _⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i⟩, hp⟩
