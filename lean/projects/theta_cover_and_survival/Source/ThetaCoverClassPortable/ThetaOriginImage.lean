import ThetaCoverClassPortable.ThetaBoundary
import ThetaCoverClassPortable.ThetaSourceComparison
noncomputable section
namespace FourCorner.ThetaOriginImage
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaActualPoints ThetaProjection
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
abbrev fC := boundaryEvaluation (k:=ℚ) (fun _=>true)
abbrev sEv := ThetaHomogeneousEvaluation.affineEvaluation (sourceEquation ℚ) 3
lemma origin_value (a : Fin 3) : fC (sEv (X a.castSucc.castSucc))=1 := by
  fin_cases a
  all_goals have hd0 : ThetaAmbientChart.drop 4 (3:Fin 5) 0=0 := by decide
  all_goals have hd1 : ThetaAmbientChart.drop 4 (3:Fin 5) 1=1 := by decide
  all_goals have hd2 : ThetaAmbientChart.drop 4 (3:Fin 5) 2=2 := by decide
  all_goals simp [fC,sEv,ThetaHomogeneousEvaluation.affineEvaluation,ThetaAmbientChart.dehom,hd0,hd1,hd2,
    boundaryEvaluation_X,sourceValues,sign]
lemma origin_p_open : originC (k:=ℚ) ⁻¹ᵁ Proj.basicOpen sG (sx (k:=ℚ) 0)=⊤ := by
  have h:=ThetaHomogeneousEvaluation.point_preimage (sourceEquation ℚ) (source_homogeneous ℚ)
    3 fC (X 0) (isHomogeneous_X ℚ 0) one_pos
  change _=PrimeSpectrum.basicOpen (fC (sEv (X 0))) at h
  have h0 : fC (sEv (X (0:Fin 5)))=1 := origin_value 0
  rw [h0,PrimeSpectrum.basicOpen_one] at h
  exact h
lemma origin_difference_zero (a : Fin 3) : originC (k:=ℚ) ⁻¹ᵁ
    Proj.basicOpen sG (sqmap (k:=ℚ) (X a.castSucc.castSucc-X 0))=⊥ := by
  have h:=ThetaHomogeneousEvaluation.point_preimage (sourceEquation ℚ) (source_homogeneous ℚ)
    3 fC (X a.castSucc.castSucc-X 0) ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)) one_pos
  change _=PrimeSpectrum.basicOpen (fC (sEv (X a.castSucc.castSucc-X 0))) at h
  have h0 : fC (sEv (X (0:Fin 5)))=1 := origin_value 0
  have hz : fC (sEv (X a.castSucc.castSucc-X 0))=0 := by rw [map_sub,map_sub,origin_value a,h0,sub_self]
  rw [hz,PrimeSpectrum.basicOpen_zero] at h
  exact h
abbrev image : Spec (.of ℚ) ⟶ D ℚ := originC ≫ projection
lemma image_z_open : image ⁻¹ᵁ Proj.basicOpen dG (dqmap (X (2:Fin 3)))=⊤ := by
  rw [image,Scheme.Hom.comp_preimage,projection_preimage,coordinateMap_X]
  exact origin_p_open
lemma image_difference_zero (a : Fin 2) : image ⁻¹ᵁ
    Proj.basicOpen dG (dqmap (X a.castSucc-X 2))=⊥ := by
  rw [image,Scheme.Hom.comp_preimage,projection_preimage]
  have he : coordinateMap (k:=ℚ) (dqmap (k:=ℚ) (X a.castSucc-X 2))=sqmap (k:=ℚ) (X (![1,2] a : Fin 5)-X 0) := by
    rw [map_sub,map_sub,coordinateMap_X,coordinateMap_X]
    fin_cases a <;> simp [sx]
  rw [he]
  fin_cases a
  · exact origin_difference_zero 1
  · exact origin_difference_zero 2
lemma image_factor : ∃ f : affineRing (targetEquation ℚ) 2 →ₐ[ℚ] ℚ,
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      (chartIso (targetEquation ℚ) (target_homogeneous ℚ) 2).inv ≫
      (Proj.basicOpen dG (dqmap (X (2:Fin 3)))).ι=image := by
  let U : (D ℚ).Opens:=Proj.basicOpen dG (dqmap (X (2:Fin 3)))
  have hr : Set.range image⊆Set.range U.ι := by
    rintro _ ⟨x,rfl⟩
    refine ⟨⟨image x,?_⟩,rfl⟩
    change x∈image ⁻¹ᵁ U
    rw [image_z_open];trivial
  let q:=IsOpenImmersion.lift U.ι image hr
  have hq : q ≫ U.ι=image:=IsOpenImmersion.lift_fac U.ι image hr
  have hp : image ≫ dToBase ℚ=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)) :=
    ThetaSourceComparison.rational_base_unique _ _
  exact ThetaPointAPI.algebra_of_chart_factor (targetEquation ℚ) (target_homogeneous ℚ) image hp 2 q hq

/-- Both displayed rational points are actual scheme points, and the actual projection maps them. -/
theorem origin_image : originC (k:=ℚ) ≫ projection=originD := by
  obtain ⟨f,hf⟩:=image_factor
  have hv (a : Fin 2) : f (Ideal.Quotient.mk _ (X a))=1 := by
    have hpre:=ThetaHomogeneousEvaluation.point_preimage (targetEquation ℚ) (target_homogeneous ℚ)
      2 f (X a.castSucc-X 2) ((isHomogeneous_X _ _).sub (isHomogeneous_X _ _)) one_pos
    have hz : PrimeSpectrum.basicOpen
        (f (ThetaHomogeneousEvaluation.affineEvaluation (targetEquation ℚ) 2 (X a.castSucc-X 2)))=⊥ := by
      rw [←hpre,hf]
      exact image_difference_zero a
    have ht:=isNilpotent_iff_eq_zero.mp ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp hz)
    have hd0 : ThetaAmbientChart.drop 2 (2:Fin 3) 0=0 := by decide
    have hd1 : ThetaAmbientChart.drop 2 (2:Fin 3) 1=1 := by decide
    fin_cases a
    all_goals simp [ThetaHomogeneousEvaluation.affineEvaluation,ThetaAmbientChart.dehom,hd0,hd1] at ht
    all_goals exact sub_eq_zero.mp ht
  have he : f=originDEvaluation := by
    apply AlgHom.ext
    intro x
    obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a => exact (f.commutes a).trans (originDEvaluation.commutes a).symm
    | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
    | mul_X p a hp =>
      have hh : f (Ideal.Quotient.mk _ (X a))=originDEvaluation (Ideal.Quotient.mk _ (X a)) := by
        rw [hv]
        change 1=MvPolynomial.aeval (fun _ : Fin 2=>(1:ℚ)) (X a)
        simp
      simpa only [map_mul] using congrArg₂ (·*·) hp hh
  change image=originD
  rw [←hf,he]
  rfl
end FourCorner.ThetaOriginImage
#print axioms FourCorner.ThetaOriginImage.origin_image
