import CriticalChartSmooth

noncomputable section
namespace FourCorner.CriticalChartBase
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open CriticalProj23 CriticalStandardCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

abbrev qmap (i : k) := CriticalQuotientChart.quotientMap (CriticalProj23.equation i) (equation_homogeneous i)
abbrev qequiv (i : k) (j : Fin 4) := CriticalQuotientChart.chartEquiv (CriticalProj23.equation i) (equation_homogeneous i) j

lemma chart_inv_ι (i : k) (j : Fin 4) :
    (chartIso i j).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι =
      Spec.map (CommRingCat.ofHom (qequiv i j).toRingHom) ≫
        Proj.awayι (criticalGrading i) (coordinate i j) (coordinate_degree_one i j) one_pos := by
  rfl

lemma base_ring_hom (i : k) (j : Fin 4) :
    (qequiv i j).toRingHom.comp ((Away.map (qmap i) (X j)).comp
      ((fromZeroRingHom (homogeneousSubmodule (Fin 4) k) (Submonoid.powers (X j))).comp
        (ambientDegreeZeroEquiv (k:=k)).toRingHom)) = algebraMap k (affineRing i j) := by
  apply RingHom.ext
  intro c
  change CriticalQuotientChart.chartDehom (CriticalProj23.equation i) (equation_homogeneous i) j
    (CriticalQuotientChart.chartQuotient (CriticalProj23.equation i) (equation_homogeneous i) j
      (algebraMap k (CriticalAmbientChart.ambientAway k j) c)) = _
  have h := RingHom.congr_fun (CriticalQuotientChart.dehom_square
    (CriticalProj23.equation i) (equation_homogeneous i) j)
    (algebraMap k (CriticalAmbientChart.ambientAway k j) c)
  simp only [RingHom.comp_apply] at h
  rw [h]
  have hc : CriticalAmbientChart.ambientDehom k j
      (algebraMap k (CriticalAmbientChart.ambientAway k j) c)=C c := by
    change CriticalAmbientChart.ambientDehom k j (Away.mk _ (Slot02HighProjSpace.X_mem_one k 3 j) 0 (C c) _)=C c
    rw [CriticalAmbientChart.ambientDehom_mk]
    simp [CriticalAmbientChart.dehom]
  rw [hc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact structural-map identity over the ORIGINAL arbitrary field k. -/
theorem chart_over_base (i : k) (j : Fin 4) :
    (chartIso i j).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι ≫ criticalToSpec i =
      Spec.map (CommRingCat.ofHom (algebraMap k (affineRing i j))) := by
  letI : GradedRing (criticalGrading i) := inferInstance
  rw [←Category.assoc,chart_inv_ι]
  change (Spec.map (CommRingCat.ofHom (qequiv i j).toRingHom) ≫
    Proj.awayι (criticalGrading i) ((qmap i) (X j)) ((qmap i).map_mem (Slot02HighProjSpace.X_mem_one k 3 j)) one_pos) ≫
    (Proj.map (qmap i) _ ≫ (Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom ambientDegreeZeroEquiv.toRingHom))) = _
  simp only [Category.assoc]
  rw [←Category.assoc (Proj.awayι _ _ _ _) (Proj.map _ _) _,
    Proj.awayι_comp_map]
  simp only [Category.assoc]
  rw [←Category.assoc (Proj.awayι _ _ _ _) (Proj.toSpecZero _) _,Proj.awayι_toSpecZero]
  rw [←Spec.map_comp,←Spec.map_comp,←Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (base_ring_hom i j))
  all_goals exact Slot02HighProjSpace.X_mem_one k 3 j

end FourCorner.CriticalChartBase
#print axioms FourCorner.CriticalChartBase.chart_over_base
