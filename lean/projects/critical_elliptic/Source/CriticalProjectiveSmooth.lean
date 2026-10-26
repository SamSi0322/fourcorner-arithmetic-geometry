import CriticalChartBase

noncomputable section
namespace FourCorner.CriticalProjectiveSmooth
open AlgebraicGeometry CategoryTheory
open CriticalProj23 CriticalStandardCharts
variable {k : Type*} [Field k]

theorem actual_chart_smooth (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (j : Fin 4) :
    SmoothOfRelativeDimension 1
      ((Proj.basicOpen (criticalGrading i) (coordinate i j)).ι ≫ criticalToSpec i) := by
  have hspec := CriticalChartSmooth.affine_smooth i hi h2 j
  have he : (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι ≫ criticalToSpec i =
      (chartIso i j).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing i j))) := by
    rw [←CriticalChartBase.chart_over_base i j]
    simp
  rw [he]
  letI := hspec
  change SmoothOfRelativeDimension (0+1)
    ((chartIso i j).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing i j))))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Native global scheme smoothness of the paper's ORIGINAL intersection of
two quadrics in P3, including every V0=0 point. No perfectness or CharZero. -/
theorem projective_smooth (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    SmoothOfRelativeDimension 1 (criticalToSpec i) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P:=(@SmoothOfRelativeDimension 1 : MorphismProperty Scheme))
    (fun j : Fin 4=>Proj.basicOpen (criticalGrading i) (coordinate i j))
    (coordinate_opens_cover i)
  exact actual_chart_smooth i hi h2
end FourCorner.CriticalProjectiveSmooth
#print axioms FourCorner.CriticalProjectiveSmooth.actual_chart_smooth
#print axioms FourCorner.CriticalProjectiveSmooth.projective_smooth
