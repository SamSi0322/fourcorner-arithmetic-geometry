import ThetaCoverClassPortable.ThetaChartAlgebras
noncomputable section
namespace FourCorner.ThetaProjectionChartMap
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ThetaLiteralModels ThetaQuotientCharts ThetaChartAlgebras
set_option maxHeartbeats 2500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
abbrev sg := ThetaProjection.sG (k:=ℚ)
abbrev dg := ThetaProjection.dG (k:=ℚ)
abbrev qmS := ThetaProjection.sqmap (k:=ℚ)
abbrev qmD := ThetaProjection.dqmap (k:=ℚ)
abbrev cm := ThetaProjection.coordinateMap (k:=ℚ)
def dden (j : Fin 3) := qmD (X (targetIndex j))
def sden (j : Fin 3) := qmS (X (sourceIndex j))
lemma denominator (j : Fin 3) : cm (dden j)=sden j := by
  rw [dden,ThetaProjection.coordinateMap_X]
  fin_cases j <;> simp [targetIndex,sourceIndex,sden,ThetaProjection.sx]
lemma polynomial_square (j : Fin 3) (p : MvPolynomial (Fin 3) ℚ) :
    ThetaAmbientChart.dehom ℚ 4 (sourceIndex j) (ThetaProjection.ambientProjection p)=
      subst j (ThetaAmbientChart.dehom ℚ 2 (targetIndex j) p) := by
  have he : (ThetaAmbientChart.dehom ℚ 4 (sourceIndex j)).comp ThetaProjection.ambientProjection.toRingHom=
      (subst j).toRingHom.comp (ThetaAmbientChart.dehom ℚ 2 (targetIndex j)) := by
    apply MvPolynomial.ringHom_ext
    · intro q;simp [ThetaAmbientChart.dehom,ThetaProjection.ambientProjection,subst]
    · intro i
      fin_cases j <;> fin_cases i
      all_goals simp [ThetaAmbientChart.dehom,ThetaProjection.ambientProjection,subst,aeval_def,
        basePolys,targetIndex,sourceIndex,ThetaActualPoints.source_drop,ThetaActualPoints.target_drop]
  exact RingHom.congr_fun he p

abbrev dDegree (j : Fin 3) : dden j∈dg 1 := qmD.map_mem (isHomogeneous_X _ _)
abbrev imageDegree (j : Fin 3) : cm (dden j)∈sg 1 := cm.map_mem (dDegree j)
def awayCongr {x y : ThetaProjection.sR (k:=ℚ)} (h : x=y) : Away sg x ≃+* Away sg y := by
  subst y
  exact RingEquiv.refl _
lemma awayCongr_mk {x y : ThetaProjection.sR (k:=ℚ)} (h : x=y) (hx : x∈sg 1) (hy : y∈sg 1)
    (d : ℕ) (p : ThetaProjection.sR (k:=ℚ)) (hp : p∈sg (d • 1)) :
    awayCongr h (Away.mk sg hx d p hp)=Away.mk sg hy d p hp := by
  subst y
  rfl
abbrev sourceDegree (j : Fin 3) : sden j∈sg 1 := qmS.map_mem (isHomogeneous_X _ _)
abbrev actualSourceEquiv (j : Fin 3) := ThetaQuotientChart.chartEquiv (sourceEquation ℚ) (source_homogeneous ℚ) (sourceIndex j)
def sourceImageEquiv (j : Fin 3) : Away sg (cm (dden j)) ≃+* S j :=
  (awayCongr (denominator j)).trans (actualSourceEquiv j)
abbrev targetEquiv (j : Fin 3) := ThetaQuotientChart.chartEquiv (targetEquation ℚ) (target_homogeneous ℚ) (targetIndex j)
lemma coordinateMap_poly (p : MvPolynomial (Fin 3) ℚ) : cm (qmD p)=qmS (ThetaProjection.ambientProjection p) := rfl

lemma image_equiv_mk (j : Fin 3) (d : ℕ) (p : MvPolynomial (Fin 3) ℚ)
    (hp : p∈homogeneousSubmodule (Fin 3) ℚ (d • 1)) :
    sourceImageEquiv j (Away.map cm (dden j)
      (Away.mk dg (dDegree j) d (qmD p) (qmD.map_mem hp)))=
      smk j (ThetaAmbientChart.dehom ℚ 4 (sourceIndex j) (ThetaProjection.ambientProjection p)) := by
  rw [Away.map_mk]
  change sourceImageEquiv j (Away.mk sg (imageDegree j) d (qmS (ThetaProjection.ambientProjection p)) _)=_
  change actualSourceEquiv j (awayCongr (denominator j)
    (Away.mk sg (imageDegree j) d (qmS (ThetaProjection.ambientProjection p)) _))=_
  rw [awayCongr_mk (denominator j) (imageDegree j) (sourceDegree j)]
  change ThetaQuotientChart.chartDehom (sourceEquation ℚ) (source_homogeneous ℚ) (sourceIndex j)
    (Away.mk sg (sourceDegree j) d (qmS (ThetaProjection.ambientProjection p)) _)=_
  rw [ThetaQuotientChart.chartDehom_mk]
  rfl
lemma away_square (j : Fin 3) :
    (sourceImageEquiv j).toRingHom.comp (Away.map cm (dden j))=
      (baseMap j).toRingHom.comp (targetEquiv j).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨d,p,hp,rfl⟩:=Away.mk_surjective dg (dDegree j) x
  obtain ⟨q,hq,rfl⟩:=(HomogeneousIdealQuotientGrading.mem_quotGrading_iff _ _).mp hp
  change sourceImageEquiv j (Away.map cm (dden j) (Away.mk dg (dDegree j) d (qmD q) (qmD.map_mem hq)))=_
  rw [image_equiv_mk j d q hq]
  change _=baseMap j (ThetaQuotientChart.chartDehom (targetEquation ℚ) (target_homogeneous ℚ) (targetIndex j)
    (Away.mk dg (dDegree j) d (qmD q) (qmD.map_mem hq)))
  rw [ThetaQuotientChart.chartDehom_mk]
  change _=baseMap j (rq j (ThetaAmbientChart.dehom ℚ 2 (targetIndex j) q))
  rw [baseMap_rq,polynomial_square]

abbrev U (j : Fin 3) := Proj.basicOpen sg (cm (dden j))
abbrev V (j : Fin 3) := Proj.basicOpen dg (dden j)
def sourceChartIso (j : Fin 3) : (U j).toScheme ≅ Spec (.of (S j)) :=
  Proj.basicOpenIsoSpec sg _ (imageDegree j) one_pos ≪≫
    Scheme.Spec.mapIso ((sourceImageEquiv j).symm.toCommRingCatIso.op)
abbrev targetChartIso (j : Fin 3) := ThetaProjectiveModel.chartIso (targetEquation ℚ) (target_homogeneous ℚ) (targetIndex j)
lemma source_chart_inv (j : Fin 3) :
    (sourceChartIso j).inv ≫ (U j).ι=Spec.map (CommRingCat.ofHom (sourceImageEquiv j).toRingHom) ≫
      Proj.awayι sg (cm (dden j)) (imageDegree j) one_pos := rfl
lemma target_chart_inv (j : Fin 3) :
    (targetChartIso j).inv ≫ (V j).ι=Spec.map (CommRingCat.ofHom (targetEquiv j).toRingHom) ≫
      Proj.awayι dg (dden j) (dDegree j) one_pos := rfl
/-- Full actual Scheme diagram identifying the polynomially defined baseMap with π
on each of the P,Q,R source charts and all three target charts. -/
theorem chart_square (j : Fin 3) :
    (sourceChartIso j).inv ≫ (U j).ι ≫ ThetaProjection.projection=
      Spec.map (CommRingCat.ofHom (baseMap j).toRingHom) ≫ (targetChartIso j).inv ≫ (V j).ι := by
  rw [←Category.assoc,source_chart_inv,Category.assoc]
  change Spec.map (CommRingCat.ofHom (sourceImageEquiv j).toRingHom) ≫
    (Proj.awayι sg (cm (dden j)) (imageDegree j) one_pos ≫
      ThetaProjMap.Proj.map cm ThetaProjection.no_base_point)=_
  rw [ThetaProjMap.Proj.awayι_comp_map cm ThetaProjection.no_base_point one_pos (dden j) (dDegree j)]
  rw [←Category.assoc (Spec.map _) (Spec.map _) _]
  rw [target_chart_inv]
  have hm:=congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (away_square j)
  simp only [CommRingCat.ofHom_comp,Spec.map_comp] at hm
  rw [hm]
  simp only [Category.assoc]
end FourCorner.ThetaProjectionChartMap
#print axioms FourCorner.ThetaProjectionChartMap.away_square
#print axioms FourCorner.ThetaProjectionChartMap.chart_square
