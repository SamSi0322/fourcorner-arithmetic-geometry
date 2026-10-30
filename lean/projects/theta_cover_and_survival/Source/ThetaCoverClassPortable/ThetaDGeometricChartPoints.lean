import ThetaCoverClassPortable.ThetaDExactModel
import ThetaCoverClassPortable.ThetaActualPoints

namespace FourCorner.ThetaDGeometricChartPoints
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial ThetaProjectiveModel ThetaLiteralModels ThetaDGeometricModel
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

abbrev equation (j : Fin 3) (a : Fin 1) : MvPolynomial (Fin 2) ℚ :=
  ThetaQuotientChart.affineEquation (targetEquation ℚ) j a
abbrev ring (j : Fin 3) := affineRing (targetEquation ℚ) j

def evaluation (j : Fin 3) (v : Fin 2 → K) (hv : ∀a : Fin 1,MvPolynomial.aeval v (equation j a)=0) :
    ring j →ₐ[ℚ] K :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval v) (by
    have h : ThetaQuotientChart.affineIdeal (targetEquation ℚ) j ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact hv a
    exact fun x hx => h hx)

@[simp] theorem evaluation_X (j : Fin 3) (v : Fin 2 → K) (hv) (a : Fin 2) :
    evaluation j v hv (Ideal.Quotient.mk _ (X a))=v a := MvPolynomial.aeval_X _ _

/-- Actual Qbar-valued point of the ORIGINAL rational Proj curve. -/
def toOriginal (j : Fin 3) (v : Fin 2 → K) (hv : ∀a : Fin 1,MvPolynomial.aeval v (equation j a)=0) :
    Spec (.of K) ⟶ D ℚ :=
  Spec.map (CommRingCat.ofHom (evaluation j v hv).toRingHom) ≫
    (chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv ≫
      (Proj.basicOpen (grading (targetEquation ℚ) (target_homogeneous ℚ))
        (coordinate (targetEquation ℚ) (target_homogeneous ℚ) j)).ι

theorem toOriginal_over (j : Fin 3) (v : Fin 2 → K) (hv) : toOriginal j v hv ≫ dToBase ℚ=qb := by
  simp only [toOriginal,Category.assoc]
  rw [ThetaModelBase.chart_over_base,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((evaluation j v hv).toRingHom.comp (algebraMap ℚ _)))=qb
  have hc : (evaluation j v hv).toRingHom.comp (algebraMap ℚ _)=algebraMap ℚ K := by
    ext a;exact (evaluation j v hv).commutes a
  rw [hc]

/-- A point of the ACTUAL categorical Qbar pullback, with the same original
chart values. It is not a point on an unproved replacement model over Qbar. -/
def point (j : Fin 3) (v : Fin 2 → K) (hv : ∀a : Fin 1,MvPolynomial.aeval v (equation j a)=0) :
    Spec (.of K) ⟶ geometricD :=
  pullback.lift (toOriginal j v hv) (𝟙 _) (by simpa only [Category.id_comp] using toOriginal_over j v hv)

theorem point_over (j : Fin 3) (v : Fin 2 → K) (hv) : point j v hv ≫ toBase=𝟙 _ := by
  simp only [point,pullback.lift_snd]

theorem point_injective (j : Fin 3) (v w : Fin 2 → K) (hv hw)
    (he : point j v hv=point j w hw) : v=w := by
  let U := Proj.basicOpen (grading (targetEquation ℚ) (target_homogeneous ℚ))
    (coordinate (targetEquation ℚ) (target_homogeneous ℚ) j)
  let m := (chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv ≫ U.ι
  have hm : Mono m := inferInstance
  have h0 := congrArg (fun f=>f ≫ pullback.fst (dToBase ℚ) qb) he
  simp only [point,pullback.lift_fst] at h0
  have hs : Spec.map (CommRingCat.ofHom (evaluation j v hv).toRingHom)=
      Spec.map (CommRingCat.ofHom (evaluation j w hw).toRingHom) := by
    apply (cancel_mono m).mp
    exact h0
  have hr := Spec.map_injective hs
  funext a
  have hh := congrArg (fun f : CommRingCat.of (ring j) ⟶ CommRingCat.of K =>
    f.hom (Ideal.Quotient.mk _ (X a))) hr
  change evaluation j v hv (Ideal.Quotient.mk _ (X a))=evaluation j w hw (Ideal.Quotient.mk _ (X a)) at hh
  simpa only [evaluation_X] using hh

#print axioms toOriginal_over
#print axioms point_over
#print axioms point_injective
end
end FourCorner.ThetaDGeometricChartPoints
