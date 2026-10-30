import CriticalExtensionPoints

noncomputable section
namespace FourCorner.CriticalHomogeneousEvaluation
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open CriticalProj23 CriticalStandardCharts CriticalChartBase
universe u
variable {k : Type u} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def affineEvaluation (i : k) (j : Fin 4) : Ambient k →+* affineRing i j :=
  (Ideal.Quotient.mk (affineIdeal i j)).comp (CriticalAmbientChart.dehom k j)

lemma affineEvaluation_X (i : k) (j a : Fin 4) :
    affineEvaluation i j (X a)=if a=j then 1 else CriticalChartJacobian.ax i j (CriticalAmbientChart.drop j a) := by
  simp only [affineEvaluation,RingHom.comp_apply,CriticalAmbientChart.dehom,coe_eval₂Hom,eval₂_X]
  split_ifs <;> simp only [map_one,CriticalChartJacobian.ax]

/-- Pullback of every actual homogeneous principal open through an actual
standard-chart isomorphism is its literal dehomogeneous polynomial open. -/
theorem chart_preimage (i : k) (j : Fin 4) (p : Ambient k) {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : 0<d) :
    ((chartIso i j).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι) ⁻¹ᵁ
      Proj.basicOpen (criticalGrading i) ((qmap i) p)=
      PrimeSpectrum.basicOpen (affineEvaluation i j p) := by
  rw [chart_inv_ι,Scheme.Hom.comp_preimage]
  have hpre:=Proj.awayι_preimage_basicOpen (criticalGrading i) (coordinate_degree_one i j) one_pos
    ((qmap i).map_mem ((mem_homogeneousSubmodule d p).mpr hp)) hd
  erw [hpre]
  erw [SpecMap_preimage_basicOpen]
  congr 1
  change CriticalQuotientChart.chartDehom (CriticalProj23.equation i) (equation_homogeneous i) j
    (Away.mk _ (coordinate_degree_one i j) d (((qmap i) p)^1) _)=_
  erw [CriticalQuotientChart.chartDehom_mk]
  rw [pow_one]
  rfl

theorem point_preimage {L : Type u} [CommRing L] [Algebra k L]
    (i : k) (j : Fin 4) (f : affineRing i j →ₐ[k] L) (p : Ambient k) {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : 0<d) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso i j).inv ≫
      (Proj.basicOpen (criticalGrading i) (coordinate i j)).ι) ⁻¹ᵁ
      Proj.basicOpen (criticalGrading i) ((qmap i) p)=
      PrimeSpectrum.basicOpen (f (affineEvaluation i j p)) := by
  rw [Scheme.Hom.comp_preimage,chart_preimage i j p hp hd]
  exact SpecMap_preimage_basicOpen (CommRingCat.ofHom f.toRingHom) _

lemma coordinate_value {L : Type*} [Field L] [Algebra k L]
    (i : k) (j a : Fin 4) (f : affineRing i j →ₐ[k] L) :
    f (affineEvaluation i j (X a))=
      CriticalChartSmooth.normalizedVector j (fun b=>f (CriticalChartJacobian.ax i j b)) a := by
  rw [affineEvaluation_X]
  unfold CriticalChartSmooth.normalizedVector
  split_ifs <;> simp only [map_one]

def shiftPolynomial : Ambient k := X 1^2-X 0^2
abbrev shiftClass (i : k) := (qmap i) (shiftPolynomial (k:=k))
def shiftOpen (i : k) := Proj.basicOpen (criticalGrading i) (shiftClass i)
lemma shift_homogeneous : (shiftPolynomial (k:=k)).IsHomogeneous 2 :=
  (isHomogeneous_X_pow _ _).sub (isHomogeneous_X_pow _ _)

lemma shift_value {L : Type*} [Field L] [Algebra k L]
    (i : k) (j : Fin 4) (f : affineRing i j →ₐ[k] L) :
    f (affineEvaluation i j (shiftPolynomial (k:=k)))=
      CriticalElliptic23.Shift (CriticalChartSmooth.normalizedVector j (fun b=>f (CriticalChartJacobian.ax i j b))) := by
  rw [shiftPolynomial,map_sub,map_pow,map_pow,map_sub,map_pow,map_pow,coordinate_value,coordinate_value]
  rfl
end FourCorner.CriticalHomogeneousEvaluation
#print axioms FourCorner.CriticalHomogeneousEvaluation.chart_preimage
#print axioms FourCorner.CriticalHomogeneousEvaluation.point_preimage
#print axioms FourCorner.CriticalHomogeneousEvaluation.shift_value
