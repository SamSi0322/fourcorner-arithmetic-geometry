import ThetaCoverClassPortable.ThetaCoverNativeChartFields
import ThetaCoverClassPortable.ThetaCoverNonSquare
import Mathlib.FieldTheory.KummerPolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits Polynomial
namespace FourCorner.ThetaCoverNativeQuadraticField
open ThetaLiteralModels ThetaDGeometricModel ThetaCoverFunctions ThetaCoverRationalData
open ThetaCoverNativeChartFields ThetaNativeFunctionFieldMap
local instance : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : Surjective qb := ThetaDChartNaturality.qb_surjective
local instance : Surjective (pullback.fst (dToBase ℚ) qb) := inferInstance
local instance : Surjective (ThetaProjection.projection (k:=ℚ)) := ThetaProjectionDegree.projection_surjective
local instance : IsFinite (ThetaProjection.projection (k:=ℚ)) := ThetaProjectionFiniteEtale.projection_finite
local instance : Flat (ThetaProjection.projection (k:=ℚ)) := by
  letI := ThetaProjectionFiniteEtale.projection_etale
  infer_instance
local instance : IsDomain S0 := source_domain
local instance : IsDomain R0 := target_domain
local instance : Algebra targetField sourceField := (fieldMap (ThetaProjection.projection (k:=ℚ))).toAlgebra

/-- The actual original source chart's literal coordinate T/P, as an element
of the original source Scheme's NATIVE generic stalk. -/
def actualV : sourceField := sourceMap (ThetaChartAlgebras.t 0)

 theorem actualV_square : actualV^2=algebraMap targetField sourceField rationalH := by
  unfold actualV
  rw [←map_pow,ThetaChartAlgebras.source_t_sq]
  have hh:=RingHom.congr_fun actual_relative_field_square (ThetaQuotientCharts.b 0)
  change fieldMap (ThetaProjection.projection (k:=ℚ)) (targetMap (ThetaQuotientCharts.b 0))=
    sourceMap (ThetaChartAlgebras.baseMap 0 (ThetaQuotientCharts.b 0)) at hh
  rw [actual_b_is_rationalH] at hh
  exact hh.symm

 theorem native_rational_h_not_square : ¬∃f : targetField,f^2=rationalH := by
  rintro ⟨f,hf⟩
  apply ThetaCoverNonSquare.literal_h_not_square
  refine ⟨fieldMap (pullback.fst (dToBase ℚ) qb) f,?_⟩
  rw [←map_pow,hf,rationalH_image]

 theorem native_polynomial_irreducible : Irreducible (ThetaQuadraticKernel.polynomial rationalH) := by
  apply X_pow_sub_C_irreducible_of_prime (show Nat.Prime 2 by decide)
  intro f hf
  exact native_rational_h_not_square ⟨f,hf⟩

 theorem native_quadratic_isField : IsField (ThetaQuadraticKernel.Q rationalH) := by
  letI : Fact (Irreducible (ThetaQuadraticKernel.polynomial rationalH)) := ⟨native_polynomial_irreducible⟩
  exact MulEquiv.isField (Field.toIsField (AdjoinRoot (ThetaQuadraticKernel.polynomial rationalH)))
    (ThetaQuadraticKernel.adjoinEquiv rationalH).toRingEquiv.toMulEquiv

local instance : Field (ThetaQuadraticKernel.Q rationalH) := native_quadratic_isField.toField
local instance : Module.Finite targetField (ThetaQuadraticKernel.Q rationalH) := ThetaQuadraticKernel.finite rationalH

/-- Literal root map to the actual T/P of the SAME original C and SAME pi. -/
def rootToSource : ThetaQuadraticKernel.Q rationalH →ₐ[targetField] sourceField :=
  ThetaQuadraticKernel.ofRoot rationalH actualV actualV_square

 theorem rootToSource_root : rootToSource (ThetaQuadraticKernel.root rationalH)=actualV :=
  ThetaQuadraticKernel.ofRoot_root _ _ _

 theorem original_field_degree : Module.finrank targetField sourceField=2 :=
  ThetaFiniteGenericDegree.degree_two (ThetaProjection.projection (k:=ℚ))
    ThetaProjectionDegree.projection_degree_two
local instance : Module.Finite targetField sourceField :=
  Module.finite_of_finrank_pos (by rw [original_field_degree];decide)

 theorem rootToSource_bijective : Function.Bijective rootToSource := by
  have hi : Function.Injective rootToSource := rootToSource.toRingHom.injective
  have hd : Module.finrank targetField (ThetaQuadraticKernel.Q rationalH)=Module.finrank targetField sourceField := by
    rw [original_field_degree]
    simpa using Module.finrank_eq_card_basis (ThetaQuadraticKernel.basisTwo rationalH)
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=rootToSource.toLinearMap) hd).mp hi⟩

 theorem actualV_generates : Algebra.adjoin targetField ({actualV}:Set sourceField)=⊤ := by
  let A := Algebra.adjoin targetField ({actualV}:Set sourceField)
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨q,rfl⟩ := rootToSource_bijective.2 z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  induction p using MvPolynomial.induction_on with
  | C a =>
    change rootToSource (algebraMap targetField (ThetaQuadraticKernel.Q rationalH) a)∈A
    rw [AlgHom.commutes]
    exact A.algebraMap_mem a
  | add p q hp hq =>
    rw [map_add,map_add]
    exact A.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul,map_mul]
    apply A.mul_mem hp
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    change rootToSource (ThetaQuadraticKernel.root rationalH)∈A
    rw [rootToSource_root]
    exact Algebra.subset_adjoin (Set.mem_singleton _)

/-- Exact literal quadratic-field description of the actual ORIGINAL
covering function field, with the actual primitive coordinate retained. -/
def original_quadratic_field_equiv :
    ThetaQuadraticKernel.Q rationalH ≃ₐ[targetField] sourceField :=
  AlgEquiv.ofBijective rootToSource rootToSource_bijective

 theorem original_root_coordinate :
    original_quadratic_field_equiv (ThetaQuadraticKernel.root rationalH)=
      sourceMap (ThetaChartAlgebras.t 0) := rootToSource_root

/-- The actual relative embedding on the actual native generic stalks;
this is not a cover rebuilt from a root equation under a new name. -/
theorem original_relative_field_diagram :
    original_quadratic_field_equiv.toRingHom.comp
      (algebraMap targetField (ThetaQuadraticKernel.Q rationalH))=
        fieldMap (ThetaProjection.projection (k:=ℚ)) := by
  ext z
  exact original_quadratic_field_equiv.commutes z

 theorem original_generic_Spec_diagram :
    Spec.map (CommRingCat.ofHom (fieldMap (ThetaProjection.projection (k:=ℚ)))) ≫
      (D ℚ).fromSpecStalk (genericPoint (D ℚ))=
        (C ℚ).fromSpecStalk (genericPoint (C ℚ)) ≫ ThetaProjection.projection :=
  ThetaNativeFunctionFieldMap.generic_diagram _

#print axioms actualV_square
#print axioms original_quadratic_field_equiv
#print axioms original_relative_field_diagram
end FourCorner.ThetaCoverNativeQuadraticField
