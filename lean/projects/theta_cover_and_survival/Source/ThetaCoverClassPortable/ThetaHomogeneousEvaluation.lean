import ThetaCoverClassPortable.ThetaModelBase
noncomputable section
namespace FourCorner.ThetaHomogeneousEvaluation
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ThetaProjectiveModel ThetaModelBase
universe u
variable {k : Type u} [Field k] {n : ℕ} [NeZero n] {ι : Type*} {e : ℕ}
variable (v : ι → ThetaAmbientChart.ambient k n) (hv : ∀ a,(v a).IsHomogeneous e)
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def affineEvaluation (j : Fin (n+1)) : ThetaAmbientChart.ambient k n →+* affineRing v j :=
  (Ideal.Quotient.mk (ThetaQuotientChart.affineIdeal v j)).comp (ThetaAmbientChart.dehom k n j)

/-- Pullback of every actual homogeneous principal open through an actual
standard-chart isomorphism is its literal dehomogeneous polynomial open. -/
theorem chart_preimage (j : Fin (n+1)) (p : ThetaAmbientChart.ambient k n) {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : 0<d) :
    ((chartIso v hv j).inv ≫ (Proj.basicOpen (grading v hv) (coordinate v hv j)).ι) ⁻¹ᵁ
      Proj.basicOpen (grading v hv) ((qmap v hv) p)=
      PrimeSpectrum.basicOpen (affineEvaluation v j p) := by
  rw [ThetaModelBase.chart_inv_ι v hv,Scheme.Hom.comp_preimage]
  have hpre:=Proj.awayι_preimage_basicOpen (grading v hv) (coordinate_degree v hv j) one_pos
    ((qmap v hv).map_mem ((mem_homogeneousSubmodule d p).mpr hp)) hd
  erw [hpre]
  erw [SpecMap_preimage_basicOpen]
  congr 1
  change ThetaQuotientChart.chartDehom v hv j
    (Away.mk _ (coordinate_degree v hv j) d (((qmap v hv) p)^1) _)=_
  erw [ThetaQuotientChart.chartDehom_mk]
  rw [pow_one]
  rfl

theorem point_preimage {L : Type u} [CommRing L] [Algebra k L]
    (j : Fin (n+1)) (f : affineRing v j →ₐ[k] L) (p : ThetaAmbientChart.ambient k n) {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : 0<d) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (chartIso v hv j).inv ≫
      (Proj.basicOpen (grading v hv) (coordinate v hv j)).ι) ⁻¹ᵁ
      Proj.basicOpen (grading v hv) ((qmap v hv) p)=
      PrimeSpectrum.basicOpen (f (affineEvaluation v j p)) := by
  rw [Scheme.Hom.comp_preimage,chart_preimage v hv j p hp hd]
  exact SpecMap_preimage_basicOpen (CommRingCat.ofHom f.toRingHom) _


end FourCorner.ThetaHomogeneousEvaluation
#print axioms FourCorner.ThetaHomogeneousEvaluation.point_preimage
