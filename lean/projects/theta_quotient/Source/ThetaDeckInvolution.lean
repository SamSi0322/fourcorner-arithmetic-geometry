import ThetaInvolutionChart
import ThetaProjectionDegree
noncomputable section
namespace FourCorner.ThetaDeckInvolution
open Algebra AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ThetaLiteralModels ThetaQuotientCharts ThetaChartAlgebras ThetaProjectionChartMap
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
abbrev W:=ThetaInvolutionChart.W
abbrev posIso:=ThetaInvolutionChart.chartIso
lemma awayCongr_awayι {x y : ThetaProjection.sR (k:=ℚ)} (h : x=y) (hx : x∈sg 1) (hy : y∈sg 1) :
    Spec.map (CommRingCat.ofHom (awayCongr h).toRingHom) ≫ Proj.awayι sg x hx one_pos=
      Proj.awayι sg y hy one_pos := by
  subst y
  simp [awayCongr]
lemma positive_chart (j : Fin 3) :
    (sourceChartIso j).inv ≫ (U j).ι=(posIso j).inv ≫ (W j).ι := by
  rw [source_chart_inv,ThetaInvolutionChart.chart_inv]
  change Spec.map (CommRingCat.ofHom ((actualSourceEquiv j).toRingHom.comp (awayCongr (denominator j)).toRingHom)) ≫
      Proj.awayι sg (cm (dden j)) (imageDegree j) one_pos=_
  rw [CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,awayCongr_awayι]
lemma positive_projection (j : Fin 3) :
    (posIso j).inv ≫ (W j).ι ≫ ThetaProjection.projection=
      Spec.map (CommRingCat.ofHom (baseMap j).toRingHom) ≫ (targetChartIso j).inv ≫ (V j).ι := by
  have h:=chart_square j
  rw [←Category.assoc,positive_chart,Category.assoc] at h
  exact h
lemma source_cover : ⨆ j : Fin 3,W j=⊤ := by
  have h:=(ThetaProjection.projection (k:=ℚ)).iSup_preimage_eq_top ThetaProjectionFiniteEtale.target_cover
  change (⨆ j : Fin 3,U j)=⊤ at h
  simpa only [U,W,ThetaInvolutionChart.W,denominator] using h
lemma invariant_base (j : Fin 3) : (ThetaInvolutionChart.nn j).toRingHom.comp (baseMap j).toRingHom=(baseMap j).toRingHom := by
  apply RingHom.ext
  intro r
  exact (ThetaInvolutionChart.nn j).commutes r
/-- Exact invariance of the actual global projection under the displayed actual scheme involution. -/
theorem sigma_projection : ThetaInvolution.sigma (k:=ℚ) ≫ ThetaProjection.projection=ThetaProjection.projection := by
  let cov:=(C ℚ).openCoverOfIsOpenCover W source_cover
  refine cov.hom_ext _ _ fun j=>?_ 
  change Fin 3 at j
  apply (cancel_epi (posIso j).inv).mp
  change (posIso j).inv ≫ (W j).ι ≫ (ThetaInvolution.sigma ≫ ThetaProjection.projection)=
    (posIso j).inv ≫ (W j).ι ≫ ThetaProjection.projection
  have hh:=congrArg (fun f=>f ≫ ThetaProjection.projection) (ThetaInvolutionChart.chart_sigma j)
  simp only [Category.assoc] at hh
  rw [hh,positive_projection]
  have hspec:=congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (invariant_base j)
  simp only [CommRingCat.ofHom_comp,Spec.map_comp] at hspec
  rw [←Category.assoc (Spec.map _) (Spec.map _) _,hspec]

/-- No geometric field-valued point of the ORIGINAL source is fixed by the actual involution. -/
theorem no_fixed_point (K : Type) [Field K] (x : Spec (.of K) ⟶ C ℚ)
    (hfixed : x ≫ ThetaInvolution.sigma=x) : False := by
  let z : Spec (.of K):=Classical.choice inferInstance
  have hz : x z∈⨆ j : Fin 3,W j := by rw [source_cover];trivial
  obtain ⟨j,hj⟩:=TopologicalSpace.Opens.mem_iSup.mp hz
  have hr : Set.range x⊆Set.range (W j).ι := by
    rintro _ ⟨z',rfl⟩
    have he : z'=z:=Subsingleton.elim _ _
    exact ⟨⟨x z',by simpa only [he] using hj⟩,rfl⟩
  let q:=IsOpenImmersion.lift (W j).ι x hr
  have hq : q ≫ (W j).ι=x:=IsOpenImmersion.lift_fac _ _ hr
  let r:=q ≫ (posIso j).hom
  let g : S j →+* K:=(Spec.homEquiv r).hom
  have hg : Spec.map (CommRingCat.ofHom g)=r:=Spec.homEquiv.symm_apply_apply r
  have hf : Spec.map (CommRingCat.ofHom g) ≫ (posIso j).inv ≫ (W j).ι=x := by
    rw [hg]
    simp only [r,Category.assoc,Iso.hom_inv_id_assoc]
    exact hq
  let f:=(posIso j).inv ≫ (W j).ι
  have hl : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom (ThetaInvolutionChart.nn j).toRingHom)=
      Spec.map (CommRingCat.ofHom g) := by
    apply (cancel_mono f).mp
    calc
      _=Spec.map (CommRingCat.ofHom g) ≫
          (Spec.map (CommRingCat.ofHom (ThetaInvolutionChart.nn j).toRingHom) ≫ (posIso j).inv ≫ (W j).ι) := by simp only [f,Category.assoc]
      _=Spec.map (CommRingCat.ofHom g) ≫ ((posIso j).inv ≫ (W j).ι ≫ ThetaInvolution.sigma) := by rw [ThetaInvolutionChart.chart_sigma]
      _=x ≫ ThetaInvolution.sigma := by rw [←hf];simp only [Category.assoc]
      _=x:=hfixed
      _=Spec.map (CommRingCat.ofHom g) ≫ f:=hf.symm
  have heC : CommRingCat.ofHom (g.comp (ThetaInvolutionChart.nn j).toRingHom)=CommRingCat.ofHom g := by
    apply Spec.map_injective
    simpa only [CommRingCat.ofHom_comp,Spec.map_comp] using hl
  have he:=congrArg CommRingCat.Hom.hom heC
  have hu:=RingHom.congr_fun he (u j)
  have ht:=RingHom.congr_fun he (t j)
  change g (ThetaInvolutionChart.nn j (u j))=g (u j) at hu
  change g (ThetaInvolutionChart.nn j (t j))=g (t j) at ht
  have hnu : ThetaInvolutionChart.nn j (u j)= -u j := ThetaPairInvariants.negate_u (ThetaSourcePairData.data j)
  have hnt : ThetaInvolutionChart.nn j (t j)= -t j := ThetaPairInvariants.negate_v (ThetaSourcePairData.data j)
  rw [hnu,map_neg] at hu
  rw [hnt,map_neg] at ht
  have h2 : IsUnit (2:K) := by simpa only [map_ofNat] using (ThetaChartFiniteEtale.two_unit (S j)).map g
  have zero_of_neg (a : K) (ha : -a=a) : a=0 := by
    apply h2.mul_left_cancel
    have hh : (2:K)*a=0 := by linear_combination -ha
    simpa only [mul_zero] using hh
  have hgu:=zero_of_neg _ hu
  have hgt:=zero_of_neg _ ht
  have hh:=congrArg g (source_unit j)
  have hbad : (0:K)=1 := by
    simpa only [map_add,map_mul,map_pow,map_one,hgu,hgt,zero_pow (by decide : 2≠0),mul_zero,zero_add] using hh
  exact zero_ne_one hbad
end FourCorner.ThetaDeckInvolution
#print axioms FourCorner.ThetaDeckInvolution.sigma_projection
#print axioms FourCorner.ThetaDeckInvolution.no_fixed_point
