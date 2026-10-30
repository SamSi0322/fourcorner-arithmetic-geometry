import HpLiteralIntegral
import SmoothCurveFieldIso
import SchemeFieldBaseChange

namespace FourCorner.HpLiteralFieldIdentification
open AlgebraicGeometry CategoryTheory AlgebraicCurve HomogeneousLocalization
open HpLiteralProjective HpTwoChartCover
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

abbrev affineZ (p : K) : (curve K p).Opens := Proj.basicOpen (G K p) (coordinate K p 0)

theorem affineZ_nonempty (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : Nonempty (affineZ K p) := by
  letI := HpLiteralIntegral.ZRing_isDomain K p hp ha hb
  exact Nonempty.map (Proj.basicOpenIsoSpec (G K p) (coordinate K p 0) (degree K p 0) one_pos).inv.base inferInstance

/-- Genuine function field of the WHOLE literal projective intersection,
identified through its proved nonempty integral affine Z-chart. -/
def functionFieldEquiv (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    letI := HpLiteralIntegral.integral K p hp ha hb
    HpLiteralField.field K p ≃+* (curve K p).functionField := by
  letI := HpLiteralIntegral.integral K p hp ha hb
  letI := HpAffineEquiv.affine_isDomain K p hp ha hb
  letI : Algebra (HpAffineUniversal.B K p) (HpLiteralField.field K p) := HpAffineFractionField.affineAlgebra K p
  letI := HpAffineFractionField.isFractionRing K p hp ha hb
  haveI := affineZ_nonempty K p hp ha hb
  have hza : IsAffineOpen (affineZ K p) := Proj.isAffineOpen_basicOpen (G K p) _ (degree K p 0) one_pos
  haveI : IsFractionRing Γ(curve K p,affineZ K p) (curve K p).functionField :=
    functionField_isFractionRing_of_isAffineOpen (curve K p) (affineZ K p) hza
  let e0 : HpLiteralIntegral.ZRing K p ≃+* Γ(curve K p,affineZ K p) :=
    (Proj.basicOpenIsoAway (G K p) (coordinate K p 0) (degree K p 0) one_pos).commRingCatIsoToRingEquiv
  let e : HpAffineUniversal.B K p ≃+* Γ(curve K p,affineZ K p) :=
    (ThetaQuotientChart.chartEquiv (equation K p) (homogeneous K p) 0).symm.trans e0
  exact IsFractionRing.ringEquivOfRingEquiv e

/-- Actual isomorphism over Q between the literal P4 three-quadric C_p and
the previously used canonical smooth proper model of its exact field.
It is deduced from proved integrality, smoothness, properness, and the actual
function-field equivalence, rather than imposed as an identification. -/
theorem literal_model_iso (p : ℚ) (hp : 1<p) :
    ∃e : curve ℚ p ≅ HpSchemeModel.curve p,e.hom ≫ HpSchemeModel.toBase p=toBase ℚ p := by
  letI := HpLiteralIntegral.integral ℚ p (by linarith) (by linarith) (by linarith)
  letI := HpLiteralSmooth.smooth p (by linarith) (by linarith) (by linarith)
  letI := HpLiteralProjective.proper ℚ p
  haveI := HpSchemeModel.model_integral p
  haveI := HpSchemeModel.model_smooth p
  haveI := HpSchemeModel.model_proper p
  letI := SmoothCurveExtension.fieldAlgebra (toBase ℚ p)
  letI := SmoothCurveExtension.fieldAlgebra (HpSchemeModel.toBase p)
  letI : Algebra ℚ (HpSchemeModel.field p) := HpSchemeModel.modelFieldAlgebra p
  let er : (HpSchemeModel.curve p).functionField ≃+* (curve ℚ p).functionField :=
    (HpSchemeModel.model p).ffEquiv.symm.trans (functionFieldEquiv ℚ p (by linarith) (by linarith) (by linarith))
  let e : (HpSchemeModel.curve p).functionField ≃ₐ[ℚ] (curve ℚ p).functionField :=
    AlgEquiv.ofRingEquiv (f:=er) (fun q=>RingHom.congr_fun
      (Subsingleton.elim (er.toRingHom.comp (algebraMap ℚ (HpSchemeModel.curve p).functionField))
        (algebraMap ℚ (curve ℚ p).functionField)) q)
  obtain ⟨e,he,_⟩ := SmoothCurveExtension.iso_of_functionField_algEquiv (toBase ℚ p) (HpSchemeModel.toBase p) e
  exact ⟨e,he⟩

#print axioms functionFieldEquiv
#print axioms literal_model_iso
end
end FourCorner.HpLiteralFieldIdentification
