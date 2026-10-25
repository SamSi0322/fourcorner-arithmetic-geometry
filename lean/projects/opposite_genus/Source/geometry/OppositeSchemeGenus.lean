import geometry.OppositeSchemeModel
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv

noncomputable section
namespace FourCorner.OppositeSchemeModel
open AlgebraicCurve OppositePolynomials
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The actual generic-point-stalk function field of the constructed scheme has
genus five; the invariant is transported through the constructed field equivalence. -/
theorem model_functionField_genus_five {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    letI := (model mu nu).functionFieldAlgebra
    genusFF K (model mu nu).C.functionField = 5 := by
  letI := (model mu nu).functionFieldAlgebra
  have htrans := genusFF_eq_of_algEquiv (functionFieldEquiv mu nu)
  exact htrans.symm.trans (OppositeAffineModel.genus_actual_fractionField hmu hnu hA hB hS)

/-- The geometric model is an actual scheme constructed from the scalar-extended
literal coordinate field, not an assumed geometric object. -/
theorem rational_geometric_model_genus_five (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    letI := (model (algebraMap ℚ (AlgebraicClosure ℚ) mu)
      (algebraMap ℚ (AlgebraicClosure ℚ) nu)).functionFieldAlgebra
    genusFF (AlgebraicClosure ℚ)
      (model (algebraMap ℚ (AlgebraicClosure ℚ) mu)
        (algebraMap ℚ (AlgebraicClosure ℚ) nu)).C.functionField = 5 := by
  letI := (model (algebraMap ℚ (AlgebraicClosure ℚ) mu)
    (algebraMap ℚ (AlgebraicClosure ℚ) nu)).functionFieldAlgebra
  have htrans := genusFF_eq_of_algEquiv (functionFieldEquiv
    (algebraMap ℚ (AlgebraicClosure ℚ) mu) (algebraMap ℚ (AlgebraicClosure ℚ) nu))
  exact htrans.symm.trans (OppositeAffineModel.rational_geometric_genus_five mu nu hnu hpos hlt)

#print axioms model_functionField_genus_five
#print axioms rational_geometric_model_genus_five
end FourCorner.OppositeSchemeModel
