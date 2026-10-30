import EllipticQuarticCover
import EllipticInfinityAffine

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]
abbrev chartRing (j : Fin 4) := CriticalQuotientChart.affineRing (equation K) j
abbrev qmap := CriticalQuotientChart.quotientMap (equation K) (homogeneous K)
abbrev qequiv (j : Fin 4) := CriticalQuotientChart.chartEquiv (equation K) (homogeneous K) j
def chartIso (j : Fin 4) :
    (Proj.basicOpen (grading K) (projectiveCoordinate K j)).toScheme ≅ Spec (.of (chartRing K j)) :=
  CriticalQuotientChart.chartSchemeIso (equation K) (homogeneous K) j
theorem coordinate_degree_one (j : Fin 4) : projectiveCoordinate K j ∈ grading K 1 :=
  HomogeneousIdealQuotientGrading.mk_mem_quotGrading _ _ (isHomogeneous_X K j)

lemma chart_inv_ι (j : Fin 4) :
    (chartIso K j).inv ≫ (Proj.basicOpen (grading K) (projectiveCoordinate K j)).ι =
      Spec.map (CommRingCat.ofHom (qequiv K j).toRingHom) ≫
        Proj.awayι (grading K) (projectiveCoordinate K j) (coordinate_degree_one K j) one_pos := by
  rfl

lemma base_ring_hom (j : Fin 4) :
    (qequiv K j).toRingHom.comp ((Away.map (qmap K) (X j)).comp
      ((fromZeroRingHom (homogeneousSubmodule (Fin 4) K) (Submonoid.powers (X j))).comp
        (CriticalProj23.ambientDegreeZeroEquiv (k:=K)).toRingHom)) =
          algebraMap K (chartRing K j) := by
  apply RingHom.ext
  intro c
  change CriticalQuotientChart.chartDehom (equation K) (homogeneous K) j
    (CriticalQuotientChart.chartQuotient (equation K) (homogeneous K) j
      (algebraMap K (CriticalAmbientChart.ambientAway K j) c)) = _
  have h := RingHom.congr_fun
    (CriticalQuotientChart.dehom_square (equation K) (homogeneous K) j)
      (algebraMap K (CriticalAmbientChart.ambientAway K j) c)
  simp only [RingHom.comp_apply] at h
  rw [h]
  have hc : CriticalAmbientChart.ambientDehom K j
      (algebraMap K (CriticalAmbientChart.ambientAway K j) c) = C c := by
    change CriticalAmbientChart.ambientDehom K j
      (Away.mk _ (Slot02HighProjSpace.X_mem_one K 3 j) 0 (C c) _) = C c
    rw [CriticalAmbientChart.ambientDehom_mk]
    simp [CriticalAmbientChart.dehom]
  rw [hc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem chart_over_base (j : Fin 4) :
    (chartIso K j).inv ≫ (Proj.basicOpen (grading K) (projectiveCoordinate K j)).ι ≫ toBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K j))) := by
  rw [←Category.assoc,chart_inv_ι]
  change (Spec.map (CommRingCat.ofHom (qequiv K j).toRingHom) ≫
    Proj.awayι (grading K) ((qmap K) (X j))
      ((qmap K).map_mem (Slot02HighProjSpace.X_mem_one K 3 j)) one_pos) ≫
    (Proj.map (qmap K) _ ≫ (Proj.toSpecZero _ ≫
      Spec.map (CommRingCat.ofHom CriticalProj23.ambientDegreeZeroEquiv.toRingHom))) = _
  simp only [Category.assoc]
  rw [←Category.assoc (Proj.awayι _ _ _ _) (Proj.map _ _) _,Proj.awayι_comp_map]
  simp only [Category.assoc]
  rw [←Category.assoc (Proj.awayι _ _ _ _) (Proj.toSpecZero _) _,Proj.awayι_toSpecZero]
  rw [←Spec.map_comp,←Spec.map_comp,←Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (base_ring_hom K j))
  all_goals exact Slot02HighProjSpace.X_mem_one K 3 j

def zeroNativeIso : (Proj.basicOpen (grading K) (projectiveCoordinate K 0)).toScheme ≅
    Spec (.of (CriticalEllipticField.ring K)) :=
  chartIso K 0 ≪≫ Scheme.Spec.mapIso ((affineEquiv K).symm.toRingEquiv.toCommRingCatIso.op)

def infinityNativeIso : (Proj.basicOpen (grading K) (projectiveCoordinate K 2)).toScheme ≅
    Spec (.of (CriticalEllipticField.ring K)) :=
  chartIso K 2 ≪≫ Scheme.Spec.mapIso ((Infinity.affineEquiv K).symm.toRingEquiv.toCommRingCatIso.op)

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.chart_over_base
#print axioms FourCorner.EllipticQuarticModel.zeroNativeIso
#print axioms FourCorner.EllipticQuarticModel.infinityNativeIso
