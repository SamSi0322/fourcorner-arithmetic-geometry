import ThetaCoverClassPortable.OppositePostPSmooth
import ThetaCoverClassPortable.OppositePostRationalChartSmooth
import ThetaCoverClassPortable.OppositePostTwoChartCover

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace FourCorner.OppositeProjective.PostSmooth
open OppositePolynomials

abbrev rationalP (mu nu : ℚ) :=
  Ideal.Quotient.mk (OppositeHomogeneousQuadrics.ideal mu nu) (X (0 : Fin 5))

lemma rational_PchartIso_over (mu nu : ℚ) :
    (PostPChart.chartSchemeIso mu nu).inv ≫
      (Proj.basicOpen (quotientGrading mu nu) (rationalP mu nu)).ι ≫ toBase mu nu =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (PostPChart.affineRing mu nu))) := by
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

theorem actual_rational_Pchart_smooth (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    SmoothOfRelativeDimension 1
      ((Proj.basicOpen (quotientGrading mu nu) (rationalP mu nu)).ι ≫ toBase mu nu) := by
  have hm : mu ≠ 0 := by intro h; simp [h] at hp
  have hspec := PostPSmooth.affine_smooth hm hn (rational_A_ne_zero mu nu hn) (rational_S_ne_zero mu nu hn)
  have heq : (Proj.basicOpen (quotientGrading mu nu) (rationalP mu nu)).ι ≫ toBase mu nu =
      (PostPChart.chartSchemeIso mu nu).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (PostPChart.affineRing mu nu))) := by
    rw [← rational_PchartIso_over mu nu]
    simp
  rw [heq]
  letI := hspec
  change SmoothOfRelativeDimension (0 + 1)
    ((PostPChart.chartSchemeIso mu nu).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (PostPChart.affineRing mu nu))))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Global smoothness of the actual literal three-quadric projective curve.
Both genuine standard charts, including their entire infinity locus, are proved smooth. -/
theorem literal_projective_smooth (mu nu : ℚ) (hn : nu ≠ 0)
    (hp : 0 < mu/nu) (hl : mu/nu < 2) :
    SmoothOfRelativeDimension 1 (OppositeProjective.toBase mu nu) := by
  let U : Bool → (curve mu nu).Opens := fun b =>
    if b then Proj.basicOpen (quotientGrading mu nu) (rationalT mu nu)
    else Proj.basicOpen (quotientGrading mu nu) (rationalP mu nu)
  have hU : iSup U = ⊤ := by
    have hcover : Proj.basicOpen (quotientGrading mu nu) (rationalT mu nu) ⊔
        Proj.basicOpen (quotientGrading mu nu) (rationalP mu nu) = ⊤ :=
      PostChart.two_charts_cover mu nu
    change (⨆ b : Bool, if b then Proj.basicOpen (quotientGrading mu nu) (rationalT mu nu)
      else Proj.basicOpen (quotientGrading mu nu) (rationalP mu nu)) = ⊤
    rw [iSup_bool_eq]
    simpa using hcover
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := (@SmoothOfRelativeDimension 1 : MorphismProperty Scheme)) U hU
  intro b
  cases b
  · exact actual_rational_Pchart_smooth mu nu hn hp hl
  · exact actual_rational_Tchart_smooth mu nu hn hp hl

end FourCorner.OppositeProjective.PostSmooth
#print axioms FourCorner.OppositeProjective.PostSmooth.actual_rational_Pchart_smooth
#print axioms FourCorner.OppositeProjective.PostSmooth.literal_projective_smooth
