import ThetaCoverClassPortable.ThetaLiteralModels
import ThetaCoverClassPortable.ThetaModelBase
noncomputable section
namespace FourCorner.ThetaActualPoints
open AlgebraicGeometry CategoryTheory MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel
variable {k : Type*} [Field k] [CharZero k]
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
lemma source_drop (j a : Fin 5) : ThetaAmbientChart.drop 4 j a =
    ![![0,0,1,2,3],![0,0,1,2,3],![0,1,0,2,3],![0,1,2,0,3],![0,1,2,3,0]] j a := by
  fin_cases j <;> fin_cases a <;> decide
lemma target_drop (j a : Fin 3) : ThetaAmbientChart.drop 2 j a =
    ![![0,0,1],![0,0,1],![0,1,0]] j a := by
  fin_cases j <;> fin_cases a <;> decide
def sign (b : Bool) : k := if b then 1 else -1
lemma sign_sq (b : Bool) : (sign (k:=k) b)^2=1 := by cases b <;> norm_num [sign]
def sourceValues (e : Fin 3 → Bool) : Fin 4 → k := ![sign (e 0),sign (e 1),sign (e 2),0]
def boundaryEvaluation (e : Fin 3 → Bool) :
    affineRing (sourceEquation k) 3 →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (sourceValues (k:=k) e)) (by
    have h : ThetaQuotientChart.affineIdeal (sourceEquation k) 3 ≤
        RingHom.ker (MvPolynomial.aeval (sourceValues (k:=k) e)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      fin_cases a
      all_goals simp [ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,sourceEquation,source_drop,
        sourceValues,sign_sq,map_ofNat]
    exact fun x hx=>h hx)
@[simp] lemma boundaryEvaluation_X (e : Fin 3 → Bool) (a : Fin 4) :
    boundaryEvaluation e (Ideal.Quotient.mk _ (X a))=sourceValues (k:=k) e a :=
  MvPolynomial.aeval_X _ _
/-- These are actual k-valued points of the literal theta Proj, in its z=1 chart. -/
def boundaryPoint (e : Fin 3 → Bool) : Spec (.of k) ⟶ C k :=
  Spec.map (CommRingCat.ofHom (boundaryEvaluation e).toRingHom) ≫
    (chartIso (sourceEquation k) (source_homogeneous k) 3).inv ≫
      (Proj.basicOpen (grading (sourceEquation k) (source_homogeneous k))
        (coordinate (sourceEquation k) (source_homogeneous k) 3)).ι
lemma boundaryPoint_over (e : Fin 3 → Bool) : boundaryPoint (k:=k) e ≫ cToBase k=𝟙 _ := by
  simp only [boundaryPoint,Category.assoc]
  rw [ThetaModelBase.chart_over_base,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((boundaryEvaluation e).toRingHom.comp (algebraMap k _)))=𝟙 _
  have hc : (boundaryEvaluation e).toRingHom.comp (algebraMap k _)=RingHom.id k := by
    ext a;exact (boundaryEvaluation e).commutes a
  rw [hc]
  simp only [CommRingCat.ofHom_id,Spec.map_id]
/-- The actual rational scheme point represented by [1:1:1:1:0]. -/
def originC : Spec (.of k) ⟶ C k := boundaryPoint (fun _=>true)

def originDEvaluation : affineRing (targetEquation k) 2 →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun _=>1)) (by
    have h : ThetaQuotientChart.affineIdeal (targetEquation k) 2 ≤
        RingHom.ker (MvPolynomial.aeval (fun _=> (1:k))).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      change MvPolynomial.aeval (fun _=> (1:k)) (ThetaAmbientChart.dehom k 2 2 (targetPolynomial k))=0
      have hcomp : (MvPolynomial.aeval (fun _ : Fin 2=> (1:k))).toRingHom.comp
          (ThetaAmbientChart.dehom k 2 2)=MvPolynomial.eval (fun _ : Fin 3=> (1:k)) := by
        apply MvPolynomial.ringHom_ext
        · intro c;simp [ThetaAmbientChart.dehom]
        · intro j
          simp only [RingHom.comp_apply,ThetaAmbientChart.dehom,coe_eval₂Hom,eval₂_X]
          split_ifs <;> simp
      have he := RingHom.congr_fun hcomp (targetPolynomial k)
      change MvPolynomial.aeval (fun _ : Fin 2=> (1:k)) (ThetaAmbientChart.dehom k 2 2 (targetPolynomial k))=_ at he
      rw [he]
      norm_num [targetPolynomial]
    exact fun x hx=>h hx)
/-- The actual rational scheme point represented by [1:1:1]. -/
def originD : Spec (.of k) ⟶ D k :=
  Spec.map (CommRingCat.ofHom (originDEvaluation (k:=k)).toRingHom) ≫
    (chartIso (targetEquation k) (target_homogeneous k) 2).inv ≫
      (Proj.basicOpen (grading (targetEquation k) (target_homogeneous k))
        (coordinate (targetEquation k) (target_homogeneous k) 2)).ι
lemma originD_over : originD (k:=k) ≫ dToBase k=𝟙 _ := by
  simp only [originD,Category.assoc]
  rw [ThetaModelBase.chart_over_base,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((originDEvaluation (k:=k)).toRingHom.comp (algebraMap k _)))=𝟙 _
  have hc : (originDEvaluation (k:=k)).toRingHom.comp (algebraMap k _)=RingHom.id k := by
    ext a;exact (originDEvaluation (k:=k)).commutes a
  rw [hc]
  simp only [CommRingCat.ofHom_id,Spec.map_id]
lemma sourceValues_castSucc (e : Fin 3 → Bool) (a : Fin 3) :
    sourceValues (k:=k) e a.castSucc=sign (e a) := by fin_cases a <;> rfl
lemma sign_injective : Function.Injective (sign (k:=k)) := by
  intro a b h
  cases a <;> cases b <;> first | rfl | (exfalso; norm_num [sign] at h)
theorem boundaryPoint_injective : Function.Injective (boundaryPoint (k:=k)) := by
  intro e d h
  let v := (chartIso (sourceEquation k) (source_homogeneous k) 3).inv ≫
      (Proj.basicOpen (grading (sourceEquation k) (source_homogeneous k))
        (coordinate (sourceEquation k) (source_homogeneous k) 3)).ι
  have hv : Mono v := inferInstance
  have he : Spec.map (CommRingCat.ofHom (boundaryEvaluation (k:=k) e).toRingHom)=
      Spec.map (CommRingCat.ofHom (boundaryEvaluation (k:=k) d).toRingHom) := by
    apply (cancel_mono v).mp
    simpa only [boundaryPoint,Category.assoc] using h
  have he' := Spec.map_injective he
  apply funext
  intro a
  apply sign_injective (k:=k)
  have heval := congrArg (fun f : CommRingCat.of (affineRing (sourceEquation k) 3) ⟶ CommRingCat.of k =>
    f.hom (Ideal.Quotient.mk _ (X a.castSucc))) he'
  change boundaryEvaluation e (Ideal.Quotient.mk _ (X a.castSucc))=
    boundaryEvaluation d (Ideal.Quotient.mk _ (X a.castSucc)) at heval
  simpa only [boundaryEvaluation_X,sourceValues_castSucc] using heval
/-- Exactly eight distinct displayed points as actual rational scheme morphisms. -/
theorem displayed_boundary_card : Nat.card (Set.range (boundaryPoint (k:=k)))=8 := by
  rw [← Nat.card_congr (Equiv.ofInjective (boundaryPoint (k:=k)) boundaryPoint_injective)]
  simp
end FourCorner.ThetaActualPoints
#print axioms FourCorner.ThetaActualPoints.boundaryPoint_over
#print axioms FourCorner.ThetaActualPoints.originD_over

#print axioms FourCorner.ThetaActualPoints.boundaryPoint_injective
#print axioms FourCorner.ThetaActualPoints.displayed_boundary_card
