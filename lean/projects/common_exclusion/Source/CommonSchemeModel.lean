import CommonActualGenus
import geometry.SchemeModelFiniteExtension
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv

noncomputable section
namespace FourCorner.CommonSchemeModel
open AlgebraicCurve AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The actual smooth proper integral model of the literal four-root field,
constructed by the accepted two-chart normalization construction. -/
def model (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    CurveModel K (CommonLiteralField.field K t) := by
  letI : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) :=
    FiniteDimensional.of_finrank_pos (by
      rw [CommonLiteralField.finrank_field_eq_sixteen K ht0 ht1 htm]; norm_num)
  exact SchemeModelFiniteExtension.model K (CommonLiteralField.field K t)

theorem model_integral (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    IsIntegral (model t ht0 ht1 htm).C := inferInstance

theorem model_proper (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    IsProper (model t ht0 ht1 htm).toBase := inferInstance

theorem model_smooth (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    SmoothOfRelativeDimension 1 (model t ht0 ht1 htm).toBase := inferInstance

/-- The constructed scheme has the literal field as its actual generic stalk. -/
def functionFieldEquiv (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    letI := (model t ht0 ht1 htm).functionFieldAlgebra
    CommonLiteralField.field K t ≃ₐ[K] (model t ht0 ht1 htm).C.functionField :=
  (model t ht0 ht1 htm).ffAlgEquiv

/-- Actual genus of the generic-point function field of the constructed
geometric scheme. No genus is assigned by the scheme definition. -/
theorem geometric_model_genus_nine [IsAlgClosed K] (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    letI := (model t ht0 ht1 htm).functionFieldAlgebra
    genusFF K (model t ht0 ht1 htm).C.functionField = 9 := by
  letI := (model t ht0 ht1 htm).functionFieldAlgebra
  have hh := genusFF_eq_of_algEquiv (functionFieldEquiv t ht0 ht1 htm)
  exact hh.symm.trans (CommonLiteralField.genusFF_eq_nine ht0 ht1 htm)

#print axioms model
#print axioms model_integral
#print axioms model_proper
#print axioms model_smooth
#print axioms functionFieldEquiv
#print axioms geometric_model_genus_nine
end FourCorner.CommonSchemeModel
