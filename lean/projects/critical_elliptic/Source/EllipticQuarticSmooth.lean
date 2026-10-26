import EllipticQuarticChartBase
import EllipticQuarticChartSmooth

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]

theorem chart_smooth (j : Fin 4)
    (h : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K j))))) :
    SmoothOfRelativeDimension 1
      ((Proj.basicOpen (grading K) (projectiveCoordinate K j)).ι ≫ toBase K) := by
  have he : (Proj.basicOpen (grading K) (projectiveCoordinate K j)).ι ≫ toBase K =
      (chartIso K j).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K j))) := by
    rw [←chart_over_base K j]
    simp
  rw [he]
  letI := h
  change SmoothOfRelativeDimension (0+1)
    ((chartIso K j).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K j))))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem smooth (h2 : (2:K)≠0) : SmoothOfRelativeDimension 1 (toBase K) := by
  let U : Bool → (curve K).Opens := fun b =>
    if b then Proj.basicOpen (grading K) (projectiveCoordinate K 0)
    else Proj.basicOpen (grading K) (projectiveCoordinate K 2)
  have hU : iSup U = ⊤ := by
    simpa [U,iSup_bool_eq] using two_opens_cover K
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P:=(@SmoothOfRelativeDimension 1 : MorphismProperty Scheme)) U hU
  intro b
  cases b
  · exact chart_smooth K 2 (EllipticQuarticChartSmooth.affine_two_smooth K h2)
  · exact chart_smooth K 0 (EllipticQuarticChartSmooth.affine_zero_smooth K h2)

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.smooth
