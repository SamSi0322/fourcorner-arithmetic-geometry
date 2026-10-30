import ThetaCoverClassPortable.ThetaCoverPic0
import ThetaCoverClassPortable.ThetaLineFixedFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.ThetaCoverQuadraticCoefficientData
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaCoverFunctions ThetaCoverContacts
open ThetaGaloisSchemeField ThetaGaloisFieldAction ThetaCoverRationalData
open ThetaGaloisCanonicalPlane ThetaRootCanonicalSections ThetaOddNativeSquareContact
open ThetaOddThetaCanonicalLines ThetaActualHalfCanonicalContacts
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : HasCanonicalDivisor (K:=K) (F:=field) := hasCanonicalDivisor_of_isCurveOver
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : IsIntegral (ThetaLiteralModels.D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : Surjective qb := ThetaDChartNaturality.qb_surjective
local instance : Surjective (CategoryTheory.Limits.pullback.fst (ThetaLiteralModels.dToBase ℚ) qb) := inferInstance

/-- The actual degree-two field QQ(sqrt2), embedded by the SAME accepted
radical embedding, not by a tuple of radical labels. -/
def coefficientEmbedding : ThetaSqrtTwo →ₐ[ℚ] K :=
  ThetaLinesAbsoluteGalois.splittingEmbedding.comp (IsScalarTower.toAlgHom ℚ ThetaSqrtTwo ThetaBiquadratic)

 theorem coefficient_degree : Module.finrank ℚ ThetaSqrtTwo=2 := ThetaLineGaloisAlgebra.sqrtTwo_degree
 theorem coefficient_generator : coefficientEmbedding (QuadraticAlgebra.omega : ThetaSqrtTwo)=ThetaLinesAbsoluteGalois.r := rfl

def coefficientFieldMap : ThetaSqrtTwo →+* field := (algebraMap K field).comp coefficientEmbedding.toRingHom
 theorem coefficientFieldMap_injective : Function.Injective coefficientFieldMap := coefficientFieldMap.injective
 theorem actual_radical_is_generator_image :
    coefficientFieldMap (QuadraticAlgebra.omega : ThetaSqrtTwo)=radical := rfl

/-- The identity is explicitly over the genuine embedded quadratic
coefficient field, retaining its exact scalar and every denominator. This
is a field identity; no divisor-Pic scalar-extension interface is asserted. -/
theorem exact_embedded_quadratic_identity :
    h=((1+x/coefficientFieldMap (QuadraticAlgebra.omega : ThetaSqrtTwo))/
       (1-x/coefficientFieldMap (QuadraticAlgebra.omega : ThetaSqrtTwo)))*
      (numerator/(28*coefficientFieldMap (QuadraticAlgebra.omega : ThetaSqrtTwo)*
        (1+x/coefficientFieldMap (QuadraticAlgebra.omega : ThetaSqrtTwo))))^2 := by
  rw [actual_radical_is_generator_image]
  exact exact_cover_identity

 theorem h_fixed (σ : Gal) : fieldAut σ h=h := by
  rw [←rationalH_image]
  exact fieldAut_rational_image σ rationalH

 theorem radical_fixed (σ : Gal) (hr : σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r) :
    fieldAut σ radical=radical := by
  change fieldAut σ (algebraMap K field ThetaLinesAbsoluteGalois.r)=_
  rw [fieldAut_constants,hr]

 theorem plus_function_fixed (σ : Gal) (hr : σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r) :
    fieldAut σ ellPlus=ellPlus := by
  unfold ellPlus
  rw [map_add,map_one,map_div₀,fieldAut_x,radical_fixed σ hr]
 theorem minus_function_fixed (σ : Gal) (hr : σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r) :
    fieldAut σ ellMinus=ellMinus := by
  unfold ellMinus
  rw [map_sub,map_one,map_div₀,fieldAut_x,radical_fixed σ hr]

 theorem plus_coefficients_fixed (σ : Gal) (hr : σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r) :
    coefficientMap σ (coefficients (.affine alphaPlus 0))=coefficients (.affine alphaPlus 0) := by
  funext i
  fin_cases i <;> simp [coefficientMap,coefficients,alphaPlus,ThetaCoverContacts.r,map_div₀,map_ofNat,hr]
 theorem minus_coefficients_fixed (σ : Gal) (hr : σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r) :
    coefficientMap σ (coefficients (.affine alphaMinus 0))=coefficients (.affine alphaMinus 0) := by
  funext i
  fin_cases i <;> simp [coefficientMap,coefficients,alphaMinus,ThetaCoverContacts.r,map_div₀,map_ofNat,hr]

/-- The ACTUAL contact divisors, not only their line labels, are invariant
under the actual subgroup fixing the embedded quadratic coefficient field. -/
theorem plus_contact_divisor_fixed (σ : Gal) (hr : σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r) :
    absoluteAction σ • Bplus=Bplus := by
  have hh:=canonical_plane_divisor_transport σ (coefficients_ne_zero (.affine alphaPlus 0))
  have heq : canonicalDivisorOf (planeToField_ne_zero (coefficientMap_ne_zero σ (coefficients_ne_zero (.affine alphaPlus 0)) ))=
      canonicalDivisorOf (planeToField_ne_zero (coefficients_ne_zero (.affine alphaPlus 0))) := by
    ext w
    rw [canonicalDivisorOf_apply,canonicalDivisorOf_apply,plus_coefficients_fixed σ hr]
  rw [heq] at hh
  have hc : canonicalDivisorOf (planeToField_ne_zero (coefficients_ne_zero (.affine alphaPlus 0)))=2 • Bplus :=
    plusData.doubled_divisor
  rw [hc] at hh
  ext w
  have he:=congrArg (fun D : Divisor K field=>D w) hh
  simp only [two_nsmul,smul_add,Finsupp.add_apply] at he
  omega

 theorem minus_contact_divisor_fixed (σ : Gal) (hr : σ ThetaLinesAbsoluteGalois.r=ThetaLinesAbsoluteGalois.r) :
    absoluteAction σ • Bminus=Bminus := by
  have hh:=canonical_plane_divisor_transport σ (coefficients_ne_zero (.affine alphaMinus 0))
  have heq : canonicalDivisorOf (planeToField_ne_zero (coefficientMap_ne_zero σ (coefficients_ne_zero (.affine alphaMinus 0)) ))=
      canonicalDivisorOf (planeToField_ne_zero (coefficients_ne_zero (.affine alphaMinus 0))) := by
    ext w
    rw [canonicalDivisorOf_apply,canonicalDivisorOf_apply,minus_coefficients_fixed σ hr]
  rw [heq] at hh
  have hc : canonicalDivisorOf (planeToField_ne_zero (coefficients_ne_zero (.affine alphaMinus 0)))=2 • Bminus :=
    minusData.doubled_divisor
  rw [hc] at hh
  ext w
  have he:=congrArg (fun D : Divisor K field=>D w) hh
  simp only [two_nsmul,smul_add,Finsupp.add_apply] at he
  omega

#print axioms exact_embedded_quadratic_identity
#print axioms plus_contact_divisor_fixed
end FourCorner.ThetaCoverQuadraticCoefficientData
