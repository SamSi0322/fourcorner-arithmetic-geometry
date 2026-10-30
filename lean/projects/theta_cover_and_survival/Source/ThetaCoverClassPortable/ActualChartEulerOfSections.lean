import ThetaCoverClassPortable.ActualChartEulerForward
import ThetaCoverClassPortable.FMDUnitH1
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardChartSections

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
universe u
namespace FourCorner.ActualChartEulerOfSections

theorem unit_euler
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    {n g r : ℕ} (γ : Fin n → Fin (r-g) → SchemeHomOver (𝟙 _) c)
    (hγ : HasChartSections c γ)
    {k : Type u} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ Spec (.of R))
    (V : (pullback c x).TwoAffineOpenCover) :
    ActualChartEulerForward.chi (pullback.snd c x) V (𝟙_ _) = 1-(g:ℤ) := by
  obtain ⟨a,ha⟩ := Spec.map_surjective x
  letI : Algebra R k := a.hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k=x := ha
  subst x
  let x := Scheme.TwoAffineOpenCover.specMap R k
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : IsIntegral (pullback c x) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback _ _)
  obtain ⟨L,_,_,M,e,he,hchart⟩ := hγ k x
  obtain ⟨Kc,hRR⟩ := hchart.1
  have h1 := FMDUnitH1.field_H1_eq_of_model_RR (F.baseChange k) M e he Kc g hRR V
  have h0 := FMDUnitCohomology.finrank_H0_unit_fibre_eq_one F x V
  dsimp only [ActualChartEulerForward.chi]
  erw [h0,h1]
  norm_num

theorem chart_euler
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    {n g r : ℕ} (hgr : 2*g<r)
    (γ : Fin n → Fin (r-g) → SchemeHomOver (𝟙 _) c) (hγ : HasChartSections c γ)
    (Dγ : RelEffCartierDiv c (r-g) (𝟙 _))
    {k : Type u} [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ Spec (.of R))
    (V : (pullback (pullback.snd c (𝟙 _)) x).TwoAffineOpenCover) :
    ActualChartEulerForward.chi (fibreAt c (𝟙 _) x) V
      (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule)) = 1 := by
  exact ActualChartEulerForward.chart_twist ε F g (r-g) r (by omega) Dγ x V
    (fun W => unit_euler c ε F γ hγ x W)

#print axioms unit_euler
#print axioms chart_euler
end FourCorner.ActualChartEulerOfSections
