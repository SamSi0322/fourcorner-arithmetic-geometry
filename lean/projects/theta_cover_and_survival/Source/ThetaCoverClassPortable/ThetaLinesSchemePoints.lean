import ThetaCoverClassPortable.ThetaActualPoints
import ThetaCoverClassPortable.FourCorner.ThetaBitangentCore

namespace FourCorner.ThetaLinesSchemePoints
open AlgebraicGeometry CategoryTheory MvPolynomial ThetaProjectiveModel ThetaLiteralModels
noncomputable section
variable {k : Type*} [Field k] [CharZero k]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev equation (j : Fin 3) (a : Fin 1) : MvPolynomial (Fin 2) k :=
  ThetaQuotientChart.affineEquation (targetEquation k) j a
abbrev ring (j : Fin 3) := affineRing (targetEquation k) j

def evaluation (j : Fin 3) (v : Fin 2 → k) (hv : ∀a : Fin 1,MvPolynomial.aeval v (equation (k:=k) j a)=0) :
    ring (k:=k) j →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval v) (by
    have h : ThetaQuotientChart.affineIdeal (targetEquation k) j ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact hv a
    exact fun x hx => h hx)

@[simp] theorem evaluation_X (j : Fin 3) (v : Fin 2 → k) (hv) (a : Fin 2) :
    evaluation j v hv (Ideal.Quotient.mk _ (X a))=v a := MvPolynomial.aeval_X _ _

/-- An actual rational point of the original D in an actual affine Proj chart. -/
def point (j : Fin 3) (v : Fin 2 → k) (hv : ∀a : Fin 1,MvPolynomial.aeval v (equation (k:=k) j a)=0) :
    Spec (.of k) ⟶ D k :=
  Spec.map (CommRingCat.ofHom (evaluation j v hv).toRingHom) ≫
    (chartIso (targetEquation k) (target_homogeneous k) j).inv ≫
      (Proj.basicOpen (grading (targetEquation k) (target_homogeneous k))
        (coordinate (targetEquation k) (target_homogeneous k) j)).ι

theorem point_over (j : Fin 3) (v : Fin 2 → k) (hv) : point j v hv ≫ dToBase k=𝟙 _ := by
  simp only [point,Category.assoc]
  rw [ThetaModelBase.chart_over_base,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((evaluation j v hv).toRingHom.comp (algebraMap k _)))=𝟙 _
  have hc : (evaluation j v hv).toRingHom.comp (algebraMap k _)=RingHom.id k := by
    ext a;exact (evaluation j v hv).commutes a
  rw [hc]
  simp only [CommRingCat.ofHom_id,Spec.map_id]

theorem point_injective (j : Fin 3) (v w : Fin 2 → k) (hv hw)
    (he : point j v hv=point j w hw) : v=w := by
  let U := Proj.basicOpen (grading (targetEquation k) (target_homogeneous k))
    (coordinate (targetEquation k) (target_homogeneous k) j)
  let m := (chartIso (targetEquation k) (target_homogeneous k) j).inv ≫ U.ι
  have hm : Mono m := inferInstance
  have hs : Spec.map (CommRingCat.ofHom (evaluation j v hv).toRingHom)=
      Spec.map (CommRingCat.ofHom (evaluation j w hw).toRingHom) := by
    apply (cancel_mono m).mp
    exact he
  have hr := Spec.map_injective hs
  funext a
  have hh := congrArg (fun f : CommRingCat.of (ring (k:=k) j) ⟶ CommRingCat.of k =>
    f.hom (Ideal.Quotient.mk _ (X a))) hr
  change evaluation j v hv (Ideal.Quotient.mk _ (X a))=evaluation j w hw (Ideal.Quotient.mk _ (X a)) at hh
  simpa only [evaluation_X] using hh

theorem affine_relations (α β x : k) (hx : thetaF x 1 (α*x+β)=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![x,α*x+β] (equation (k:=k) 1 a)=0 := by
  intro a;fin_cases a
  simpa [equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,thetaF,map_ofNat,mul_assoc]
    using hx

theorem vertical_relations (t x : k) (hx : thetaF (t*x) x 1=0) :
    ∀a : Fin 1,MvPolynomial.aeval ![t*x,x] (equation (k:=k) 2 a)=0 := by
  intro a;fin_cases a
  simpa [equation,ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,
    targetEquation,targetPolynomial,ThetaActualPoints.target_drop,thetaF,map_ofNat,mul_assoc]
    using hx

/-- Contact parameters on an affine displayed line give actual points on the original D. -/
def affinePoint (α β x : k) (hx : thetaF x 1 (α*x+β)=0) : Spec (.of k) ⟶ D k :=
  point 1 ![x,α*x+β] (affine_relations α β x hx)

def verticalPoint (t x : k) (hx : thetaF (t*x) x 1=0) : Spec (.of k) ⟶ D k :=
  point 2 ![t*x,x] (vertical_relations t x hx)

theorem affinePoint_injective (α β x y : k) (hx hy) (h : affinePoint α β x hx=affinePoint α β y hy) : x=y :=
  congrFun (point_injective 1 _ _ _ _ h) 0

theorem verticalPoint_injective (t x y : k) (hx hy) (h : verticalPoint t x hx=verticalPoint t y hy) : x=y :=
  congrFun (point_injective 2 _ _ _ _ h) 1

#print axioms point_over
#print axioms point_injective
#print axioms affinePoint_injective
#print axioms verticalPoint_injective
end
end FourCorner.ThetaLinesSchemePoints
