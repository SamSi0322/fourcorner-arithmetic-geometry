import ThetaHomogeneousSign
import ThetaPairInvariants
import ThetaSourcePairData
import ThetaProjectionChartMap
noncomputable section
namespace FourCorner.ThetaInvolutionChart
open Algebra AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ThetaLiteralModels ThetaQuotientCharts ThetaChartAlgebras
open ThetaProjectionChartMap
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
abbrev ss := ThetaInvolution.sigmaMap (k:=ℚ)
abbrev nn (j : Fin 3) := ThetaPairInvariants.negate (ThetaSourcePairData.data j)
abbrev nnQ (j : Fin 3) := (nn j).restrictScalars ℚ

def tauValues (j : Fin 3) : Fin 5 → SA
  | 0=>scoords j 0
  | 1=>scoords j 1
  | 2=>scoords j 2
  | 3=> -X 2
  | 4=> -X 3
lemma canonical_coordinates (j : Fin 3) (i : Fin 4) :
    nn j (smk j (X i))=if i=2 ∨ i=3 then -smk j (X i) else smk j (X i) := by
  fin_cases i
  · change nn j (smk j (X (0:Fin 4)))=smk j (X (0:Fin 4))
    have h : smk j (X (0:Fin 4))=baseMap j (rq j (X (ThetaSourcePresentation.baseInverse j 0))) :=
      ThetaSourcePresentation.base_coordinate j 0
    rw [h]
    exact (nn j).commutes _
  · change nn j (smk j (X (1:Fin 4)))=smk j (X (1:Fin 4))
    have h : smk j (X (1:Fin 4))=baseMap j (rq j (X (ThetaSourcePresentation.baseInverse j 1))) :=
      ThetaSourcePresentation.base_coordinate j 1
    rw [h]
    exact (nn j).commutes _
  · change nn j (smk j (X (2:Fin 4)))= -smk j (X (2:Fin 4))
    rw [ThetaSourcePresentation.z_coordinate,map_sub,map_mul]
    have hu : nn j (u j)= -u j := ThetaPairInvariants.negate_u _
    have ht : nn j (t j)= -t j := ThetaPairInvariants.negate_v _
    have hc : nn j (algebraMap ℚ (S j) (shift j))=algebraMap ℚ (S j) (shift j) := (nnQ j).commutes _
    rw [hu,ht,hc]
    ring
  · exact ThetaPairInvariants.negate_v _
lemma canonical_evaluation (j : Fin 3) (p : MvPolynomial (Fin 5) ℚ) :
    nn j (smk j (ThetaAmbientChart.dehom ℚ 4 (sourceIndex j) p))=
      smk j (eval₂ C (tauValues j) p) := by
  have he : (nnQ j).toRingHom.comp ((smk j).toRingHom.comp (ThetaAmbientChart.dehom ℚ 4 (sourceIndex j)))=
      (smk j).toRingHom.comp (eval₂Hom C (tauValues j)) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp only [RingHom.comp_apply,ThetaAmbientChart.dehom,coe_eval₂Hom,eval₂_C]
      exact (nnQ j).commutes q
    · intro i
      fin_cases j <;> fin_cases i
      all_goals simp [RingHom.comp_apply,ThetaAmbientChart.dehom,sourceIndex,ThetaActualPoints.source_drop,
        tauValues,scoords,canonical_coordinates]
  exact RingHom.congr_fun he p
lemma sigma_dehom (j : Fin 3) {p : MvPolynomial (Fin 5) ℚ} {d : ℕ} (hp : p.IsHomogeneous d) :
    ThetaAmbientChart.dehom ℚ 4 (sourceIndex j) (ThetaInvolution.ambientSigma p)=
      (-1:SA)^d*eval₂ C (tauValues j) p := by
  have he : (ThetaAmbientChart.dehom ℚ 4 (sourceIndex j)).comp ThetaInvolution.ambientSigma.toRingHom=
      eval₂Hom C (fun i=> -tauValues j i) := by
    apply MvPolynomial.ringHom_ext
    · intro q;simp [ThetaAmbientChart.dehom,ThetaInvolution.ambientSigma]
    · intro i
      fin_cases j <;> fin_cases i
      all_goals simp [RingHom.comp_apply,ThetaAmbientChart.dehom,ThetaInvolution.ambientSigma,sourceIndex,
        ThetaActualPoints.source_drop,tauValues,scoords]
  rw [show ThetaAmbientChart.dehom ℚ 4 (sourceIndex j) (ThetaInvolution.ambientSigma p)=eval₂ C (fun i=> -tauValues j i) p from RingHom.congr_fun he p]
  exact ThetaHomogeneousSign.eval₂_neg C (tauValues j) hp
lemma sigma_poly (p : MvPolynomial (Fin 5) ℚ) : ss (qmS p)=qmS (ThetaInvolution.ambientSigma p) := rfl
lemma sigma_den (j : Fin 3) : ss (sden j)= -sden j := by
  rw [sden,ThetaInvolution.sigma_coordinates]
  fin_cases j <;> simp [sourceIndex,ThetaProjection.sx]
abbrev sigmaDegree (j : Fin 3) : ss (sden j)∈sg 1 := ss.map_mem (sourceDegree j)
lemma negDegree : (-1 : ThetaProjection.sR (k:=ℚ))∈sg 0 :=
  (sg 0).neg_mem (SetLike.one_mem_graded sg)
lemma neg_factor (j : Fin 3) : sden j=ss (sden j)*(-1) := by rw [sigma_den];ring
def negToPos (j : Fin 3) : Away sg (ss (sden j)) →+* Away sg (sden j) :=
  awayMap sg negDegree (neg_factor j)

lemma normalized_mk (j : Fin 3) (d : ℕ) (p : MvPolynomial (Fin 5) ℚ)
    (hp : p∈homogeneousSubmodule (Fin 5) ℚ (d • 1)) :
    actualSourceEquiv j (negToPos j (Away.map ss (sden j)
      (Away.mk sg (sourceDegree j) d (qmS p) (qmS.map_mem hp))))=
      nn j (actualSourceEquiv j (Away.mk sg (sourceDegree j) d (qmS p) (qmS.map_mem hp))) := by
  rw [Away.map_mk]
  change actualSourceEquiv j (negToPos j (Away.mk sg (sigmaDegree j) d (qmS (ThetaInvolution.ambientSigma p)) _))=_
  rw [negToPos,awayMap_mk]
  change ThetaQuotientChart.chartDehom (sourceEquation ℚ) (source_homogeneous ℚ) (sourceIndex j)
    (Away.mk sg (sourceDegree j) d (qmS (ThetaInvolution.ambientSigma p)*(-1)^d) _)=_
  rw [ThetaQuotientChart.chartDehom_mk]
  rw [map_mul,map_pow,map_neg,map_one]
  change smk j (ThetaAmbientChart.dehom ℚ 4 (sourceIndex j) (ThetaInvolution.ambientSigma p))*(-1)^d=_
  change _=nn j (ThetaQuotientChart.chartDehom (sourceEquation ℚ) (source_homogeneous ℚ) (sourceIndex j)
    (Away.mk sg (sourceDegree j) d (qmS p) _))
  rw [ThetaQuotientChart.chartDehom_mk]
  change _=nn j (smk j (ThetaAmbientChart.dehom ℚ 4 (sourceIndex j) p))
  rw [canonical_evaluation,sigma_dehom j hp]
  simp only [map_mul,map_pow,map_neg,map_one]
  have hn : ((-1:S j)^d)*((-1:S j)^d)=1 := by
    have hh : (-1:S j)*(-1:S j)=1 := by ring
    rw [←mul_pow,hh,one_pow]
  calc
    _=((-1:S j)^d*(-1:S j)^d)*smk j (eval₂ C (tauValues j) p) := by ring
    _=_ := by rw [hn,one_mul]
lemma normalized_away (j : Fin 3) :
    (actualSourceEquiv j).toRingHom.comp ((negToPos j).comp (Away.map ss (sden j)))=
      (nnQ j).toRingHom.comp (actualSourceEquiv j).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨d,p,hp,rfl⟩:=Away.mk_surjective sg (sourceDegree j) x
  obtain ⟨q,hq,rfl⟩:=(HomogeneousIdealQuotientGrading.mem_quotGrading_iff _ _).mp hp
  exact normalized_mk j d q hq

abbrev W (j : Fin 3) := Proj.basicOpen sg (sden j)
abbrev chartIso (j : Fin 3) := ThetaProjectiveModel.chartIso (sourceEquation ℚ) (source_homogeneous ℚ) (sourceIndex j)
lemma chart_inv (j : Fin 3) : (chartIso j).inv ≫ (W j).ι=
    Spec.map (CommRingCat.ofHom (actualSourceEquiv j).toRingHom) ≫
      Proj.awayι sg (sden j) (sourceDegree j) one_pos := rfl
/-- Actual scheme involution on every literal P/Q/R chart normalizes to (u,t)↦(-u,-t). -/
theorem chart_sigma (j : Fin 3) :
    (chartIso j).inv ≫ (W j).ι ≫ ThetaInvolution.sigma=
      Spec.map (CommRingCat.ofHom (nn j).toRingHom) ≫ (chartIso j).inv ≫ (W j).ι := by
  have htrans : Spec.map (CommRingCat.ofHom (negToPos j)) ≫
      Proj.awayι sg (ss (sden j)) (sigmaDegree j) one_pos=
      Proj.awayι sg (sden j) (sourceDegree j) one_pos := by
    exact Proj.SpecMap_awayMap_awayι sg (sigmaDegree j) one_pos negDegree (neg_factor j)
  conv_lhs => rw [←Category.assoc,chart_inv,Category.assoc,←htrans]
  simp only [Category.assoc]
  unfold ThetaInvolution.sigma
  rw [Proj.awayι_comp_map ss
    (ProjectiveClosedImmersion.irrelevant_le_map_of_surjective ss (ThetaInvolution.sigmaMap_surjective (k:=ℚ)))
    one_pos (sden j) (sourceDegree j)]
  rw [chart_inv]
  have hm:=congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (normalized_away j)
  simp only [CommRingCat.ofHom_comp,Spec.map_comp] at hm
  have hh:=congrArg (fun f=>f ≫ Proj.awayι sg (sden j) (sourceDegree j) one_pos) hm
  simp only [Category.assoc] at hh
  exact hh
end FourCorner.ThetaInvolutionChart
#print axioms FourCorner.ThetaInvolutionChart.chart_sigma
