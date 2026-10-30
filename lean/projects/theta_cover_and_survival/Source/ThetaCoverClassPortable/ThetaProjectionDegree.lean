import ThetaCoverClassPortable.ThetaProjectionFiniteEtale
import ThetaCoverClassPortable.ThetaPairRank
import ThetaCoverClassPortable.ThetaStdSchemeFlatRank
noncomputable section
namespace FourCorner.ThetaProjectionDegree
open AlgebraicGeometry CategoryTheory
open ThetaProjectionChartMap ThetaQuotientCharts ThetaChartAlgebras
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma chart_rank (j : Fin 3) (p : PrimeSpectrum (R j)) :
    (Spec.map (CommRingCat.ofHom (baseMap j).toRingHom)).finrank p=2 := by
  have hf:=ThetaChartFiniteEtale.chart_finite_etale j
  letI : Module.Finite (R j) (S j) := RingHom.finite_algebraMap.mp hf.1
  letI : Algebra.Etale (R j) (S j) := RingHom.etale_algebraMap.mp hf.2
  change (Spec.map (CommRingCat.ofHom (algebraMap (R j) (S j)))).finrank p=2
  rw [Scheme.Hom.finrank_SpecMap_algebraMap]
  exact ThetaPairRank.rankAtStalk (ThetaSourcePairData.data j)
    (algebraMap ℚ (R j) (lambda j)) (base_unit_ideal j) p
lemma local_pullback (j : Fin 3) :
    IsPullback (sourceChartIso j).inv
      (Spec.map (CommRingCat.ofHom (baseMap j).toRingHom))
      (ThetaProjection.projection ∣_ V j) (targetChartIso j).inv := by
  apply IsPullback.of_horiz_isIso
  constructor
  have h:=ThetaProjectionFiniteEtale.local_map j
  have hh:=congrArg (fun f=>f ≫ (targetChartIso j).inv) h
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using hh
/-- Constant native rank two of the actual global finite etale projection. -/
theorem projection_degree_two (y : ThetaLiteralModels.D ℚ) :
    (ThetaProjection.projection (k:=ℚ)).finrank y=2 := by
  letI := ThetaProjectionFiniteEtale.projection_finite
  letI := ThetaProjectionFiniteEtale.projection_etale
  have hy : y∈⨆ j : Fin 3,V j := by rw [ThetaProjectionFiniteEtale.target_cover];trivial
  obtain ⟨j,hj⟩:=TopologicalSpace.Opens.mem_iSup.mp hy
  let v : V j:=⟨y,hj⟩
  let p : Spec (.of (R j)):=(targetChartIso j).hom v
  have h1 : (ThetaProjection.projection ∣_ V j).finrank v=
      (ThetaProjection.projection (k:=ℚ)).finrank y := by
    exact Scheme.Hom.finrank_of_isPullback (ThetaProjection.projection ⁻¹ᵁ V j).ι
      (ThetaProjection.projection ∣_ V j) ThetaProjection.projection (V j).ι
      (isPullback_morphismRestrict ThetaProjection.projection (V j)).flip v
  have h2 : (Spec.map (CommRingCat.ofHom (baseMap j).toRingHom)).finrank p=
      (ThetaProjection.projection ∣_ V j).finrank v := by
    have h:=Scheme.Hom.finrank_of_isPullback (sourceChartIso j).inv
      (Spec.map (CommRingCat.ofHom (baseMap j).toRingHom))
      (ThetaProjection.projection ∣_ V j) (targetChartIso j).inv (local_pullback j) p
    have he : (targetChartIso j).inv ((targetChartIso j).hom v)=v := by
      have hh:=congrArg (fun f=>f v) (targetChartIso j).hom_inv_id
      simp only [Scheme.Hom.comp_apply] at hh
      change (targetChartIso j).inv ((targetChartIso j).hom v)=v at hh
      exact hh
    exact h.trans (congrArg (fun z : V j=>(ThetaProjection.projection ∣_ V j).finrank z) he)
  exact h1.symm.trans (h2.symm.trans (chart_rank j p))
theorem projection_surjective : Surjective (ThetaProjection.projection (k:=ℚ)) := by
  letI := ThetaProjectionFiniteEtale.projection_finite
  letI := ThetaProjectionFiniteEtale.projection_etale
  apply (Scheme.Hom.one_le_finrank_iff_surjective (ThetaProjection.projection (k:=ℚ))).mp
  intro y
  rw [projection_degree_two]
  norm_num
end FourCorner.ThetaProjectionDegree
#print axioms FourCorner.ThetaProjectionDegree.projection_degree_two
#print axioms FourCorner.ThetaProjectionDegree.projection_surjective
