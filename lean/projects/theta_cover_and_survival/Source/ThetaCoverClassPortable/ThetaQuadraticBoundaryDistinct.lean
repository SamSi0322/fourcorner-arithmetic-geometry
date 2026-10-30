import ThetaCoverClassPortable.ThetaQuadraticBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial

namespace FourCorner.ThetaQuadraticBoundaryDistinct
attribute [local instance] Classical.propDecidable
open ThetaQuadraticCurve ThetaQuadraticBoundary
local instance : IsIntegral curve := curve_integral
local instance : IsProper toBase := curve_proper
local instance : SmoothOfRelativeDimension 1 toBase := curve_smooth
local instance : Algebra F functionField := ThetaQuadraticCurve.fieldAlgebra

theorem point_injective : Function.Injective ThetaQuadraticBoundary.point := by
  intro e d he
  letI : IsOpenImmersion (ThetaDPlaneChartSections.chartMap 2) := by
    unfold ThetaDPlaneChartSections.chartMap
    infer_instance
  have h := congrArg (fun f => f ≫ toRational) he
  simp only [point_original] at h
  unfold ThetaCoverRationalData.rationalPoint at h
  change (baseMap ≫ Spec.map (CommRingCat.ofHom
      (ThetaCoverRationalData.rationalEvaluation e).toRingHom)) ≫ ThetaDPlaneChartSections.chartMap 2 =
    (baseMap ≫ Spec.map (CommRingCat.ofHom
      (ThetaCoverRationalData.rationalEvaluation d).toRingHom)) ≫ ThetaDPlaneChartSections.chartMap 2 at h
  have hs := (cancel_mono (ThetaDPlaneChartSections.chartMap 2)).mp h
  change Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) ≫ _ at hs
  rw [←Spec.map_comp,←Spec.map_comp] at hs
  have hr := Spec.map_injective hs
  have hv (a : Fin 2) : ThetaCoverRationalData.rationalValues e a =
      ThetaCoverRationalData.rationalValues d a := by
    apply (algebraMap ℚ F).injective
    have hh := congrArg (fun f : CommRingCat.of (ThetaDPlaneChartSections.chartRing 2) ⟶ .of F =>
      f.hom (Ideal.Quotient.mk _ (X a))) hr
    change algebraMap ℚ F (ThetaCoverRationalData.rationalEvaluation e (Ideal.Quotient.mk _ (X a))) =
      algebraMap ℚ F (ThetaCoverRationalData.rationalEvaluation d (Ideal.Quotient.mk _ (X a))) at hh
    simpa only [ThetaCoverRationalData.rationalEvaluation_X] using hh
  have hx := hv 0
  have hy := hv 1
  rcases e with ⟨a,b⟩
  rcases d with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> solve
    | rfl
    | norm_num [ThetaCoverRationalData.rationalValues,ThetaActualPoints.sign] at hx
    | norm_num [ThetaCoverRationalData.rationalValues,ThetaActualPoints.sign] at hy

theorem place_injective : Function.Injective ThetaQuadraticBoundary.place := by
  intro e d he
  apply point_injective
  have h : SmoothProperRationalPointPlaces.pointEquivRationalPlace toBase ⟨point e,point_over e⟩ =
      SmoothProperRationalPointPlaces.pointEquivRationalPlace toBase ⟨point d,point_over d⟩ :=
    Subtype.ext he
  exact congrArg Subtype.val ((SmoothProperRationalPointPlaces.pointEquivRationalPlace toBase).injective h)

theorem E2_apply (w : Place F functionField) : E2 w=if ∃e,place e=w then 1 else 0 := by
  classical
  by_cases hw : ∃e,place e=w
  · obtain ⟨e,rfl⟩ := hw
    rw [if_pos ⟨e,rfl⟩]
    simp only [E2,Finsupp.finsetSum_apply,Finsupp.single_apply]
    rw [Finset.sum_eq_single e]
    · simp
    · intro b _ hb
      rw [if_neg (fun hh => hb (place_injective hh))]
    · simp
  · rw [if_neg hw]
    simp only [E2,Finsupp.finsetSum_apply,Finsupp.single_apply]
    exact Finset.sum_eq_zero (fun e _ => if_neg (fun h => hw ⟨e,h⟩))

end FourCorner.ThetaQuadraticBoundaryDistinct
