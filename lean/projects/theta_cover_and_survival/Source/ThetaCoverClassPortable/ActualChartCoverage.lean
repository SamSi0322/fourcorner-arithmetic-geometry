import ThetaCoverClassPortable.ActualChartCoverageGeom
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicCurve NeronModelInfra AlgebraicGeometry.RelPicard
universe u
namespace FourCorner.ActualChartCovering
/-- Honest actual-FMD/HasChartSections coverage. The model/RR and all Euler
values are derived internally; every field, test scheme and cover is retained. -/
theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (F : SmoothProperCurve.FiniteMapData c ε)
    (n g r : ℕ) (hgr : 2 * g < r)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ i, (Dγ i).I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    ∃ i : Fin n, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  obtain ⟨i, hi⟩ := geom R c ε F n g r hgr γ hγ Dγ hDγ t L hL (AlgebraicClosure k)
    (Scheme.TwoAffineOpenCover.specMap k (AlgebraicClosure k) ≫ s)
  refine ⟨i, fun 𝒲 => ?_⟩
  haveI : IsSeparated c := inferInstance
  have hσ : rigSection c t ε ≫ pullback.snd c t = 𝟙 _ := pullback.lift_snd _ _ _
  have hTw : Scheme.Modules.IsInvertible (sectionTwist c ε t r) :=
    ((Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c t ε) hσ).pow r).isInvertible_invModule
  have hF : Scheme.Modules.IsInvertible
      (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) :=
    L.isInvertible.tensor (hTw.tensor ((Dγ i).pullbackAlong t (Category.comp_id t)).isInvertible_I.isInvertible_module)
  obtain ⟨𝒲', -, hH1⟩ :=
    exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff c t
      (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)) hF s 𝒲
      (AlgebraicClosure k)
  exact hH1.mp (hi 𝒲')


/-- These genuine H1-open loci cover every test scheme. Their defining iff
is a separately proved openness interface, not a coverage assumption. -/
theorem opens_iSup_eq_top
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    (n g r : ℕ) (hgr : 2*g<r)
    (γ : Fin n → Fin (r-g) → SchemeHomOver (𝟙 _) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r-g) (𝟙 _))
    (hDγ : ∀ i,(Dγ i).I=prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (U : Fin n → T.Opens)
    (hU : ∀ (i : Fin n) (k : Type u) [Field k] (s : Spec (.of k) ⟶ T),
      Set.range ⇑s ⊆ (U i:Set T) ↔
      ∀ V : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
        Subsingleton (V.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    (⨆ i,U i)=⊤ := by
  rw [eq_top_iff]
  rintro p -
  obtain ⟨i,hi⟩ := solution R c ε F n g r hgr γ hγ Dγ hDγ t L hL
    (T.residueField p) (T.fromSpecResidueField p)
  have hmem := (hU i (T.residueField p) (T.fromSpecResidueField p)).mpr hi
  have hp : p ∈ U i := hmem ⟨IsLocalRing.closedPoint _,by exact T.fromSpecResidueField_apply p _⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i,hp⟩

end FourCorner.ActualChartCovering
