import ThetaCoverClassPortable.ThetaProjectiveModel
import ThetaCoverClassPortable.FiniteJacobianSmooth
noncomputable section
namespace FourCorner.ThetaModelBase
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ThetaProjectiveModel
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {ι : Type*} {d : ℕ}
variable (q : ι → ThetaAmbientChart.ambient k n) (hq : ∀ i, (q i).IsHomogeneous d)
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
abbrev qmap := ThetaQuotientChart.quotientMap q hq
abbrev qequiv (j : Fin (n+1)) := ThetaQuotientChart.chartEquiv q hq j

lemma chart_inv_ι (j : Fin (n+1)) :
    (chartIso q hq j).inv ≫ (Proj.basicOpen (grading q hq) (coordinate q hq j)).ι =
      Spec.map (CommRingCat.ofHom (qequiv q hq j).toRingHom) ≫
        Proj.awayι (grading q hq) (coordinate q hq j) (coordinate_degree q hq j) one_pos := by
  rfl

lemma base_ring_hom (j : Fin (n+1)) :
    (qequiv q hq j).toRingHom.comp ((Away.map (qmap q hq) (X j)).comp
      ((fromZeroRingHom (homogeneousSubmodule (Fin (n+1)) k) (Submonoid.powers (X j))).comp
        (ambientDegreeZeroEquiv (k:=k) (n:=n)).toRingHom)) = algebraMap k (affineRing q j) := by
  apply RingHom.ext
  intro c
  change ThetaQuotientChart.chartDehom q hq j
    (ThetaQuotientChart.chartQuotient q hq j
      (algebraMap k (ThetaAmbientChart.ambientAway k n j) c)) = _
  have h := RingHom.congr_fun (ThetaQuotientChart.dehom_square
    q hq j)
    (algebraMap k (ThetaAmbientChart.ambientAway k n j) c)
  simp only [RingHom.comp_apply] at h
  rw [h]
  have hc : ThetaAmbientChart.ambientDehom k n j
      (algebraMap k (ThetaAmbientChart.ambientAway k n j) c)=C c := by
    change ThetaAmbientChart.ambientDehom k n j (Away.mk _ (Slot02HighProjSpace.X_mem_one k n j) 0 (C c) _)=C c
    rw [ThetaAmbientChart.ambientDehom_mk]
    simp [ThetaAmbientChart.dehom]
  rw [hc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact structural-map identity over the ORIGINAL arbitrary field k. -/
theorem chart_over_base (j : Fin (n+1)) :
    (chartIso q hq j).inv ≫ (Proj.basicOpen (grading q hq) (coordinate q hq j)).ι ≫ toBase q hq =
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing q j))) := by
  letI : GradedRing (grading q hq) := inferInstance
  rw [←Category.assoc,chart_inv_ι q hq]
  change (Spec.map (CommRingCat.ofHom (qequiv q hq j).toRingHom) ≫
    Proj.awayι (grading q hq) ((qmap q hq) (X j)) ((qmap q hq).map_mem (Slot02HighProjSpace.X_mem_one k n j)) one_pos) ≫
    (Proj.map (qmap q hq) _ ≫ (Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (ambientDegreeZeroEquiv (n:=n)).toRingHom))) = _
  simp only [Category.assoc]
  rw [←Category.assoc (Proj.awayι _ _ _ _) (Proj.map _ _) _,
    Proj.awayι_comp_map]
  simp only [Category.assoc]
  rw [←Category.assoc (Proj.awayι _ _ _ _) (Proj.toSpecZero _) _,Proj.awayι_toSpecZero]
  rw [←Spec.map_comp,←Spec.map_comp,←Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (base_ring_hom q hq j))
  all_goals exact Slot02HighProjSpace.X_mem_one k n j


theorem smooth (hs : ∀ j : Fin (n+1), SmoothOfRelativeDimension 1
    (Spec.map (CommRingCat.ofHom (algebraMap k (affineRing q j))))) :
    SmoothOfRelativeDimension 1 (toBase q hq) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P:=(@SmoothOfRelativeDimension 1 : MorphismProperty Scheme))
    (fun j : Fin (n+1) => Proj.basicOpen (grading q hq) (coordinate q hq j))
    (opens_cover q hq)
  intro j
  have he : (Proj.basicOpen (grading q hq) (coordinate q hq j)).ι ≫ toBase q hq =
      (chartIso q hq j).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (affineRing q j))) := by
    rw [← chart_over_base q hq j]
    simp
  rw [he]
  haveI := hs j
  change SmoothOfRelativeDimension (0+1) _
  infer_instance
end FourCorner.ThetaModelBase
#print axioms FourCorner.ThetaModelBase.chart_over_base
#print axioms FourCorner.ThetaModelBase.smooth
