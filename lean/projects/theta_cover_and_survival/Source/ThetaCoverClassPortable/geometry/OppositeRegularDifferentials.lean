import ThetaCoverClassPortable.geometry.OppositeAffineModel
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed

noncomputable section
namespace FourCorner.OppositeAffineModel
open AlgebraicCurve OppositeCoordinateAlgebra

/-- Regular rational differentials of the genuine geometric function field
form a five-dimensional vector space. -/
theorem rational_regularDiffs_finrank_five (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    Module.Finite (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ)
        (functionField (algebraMap ℚ (AlgebraicClosure ℚ) mu)
          (algebraMap ℚ (AlgebraicClosure ℚ) nu))) ∧
    Module.finrank (AlgebraicClosure ℚ)
      ↥(regularDiffs (AlgebraicClosure ℚ)
        (functionField (algebraMap ℚ (AlgebraicClosure ℚ) mu)
          (algebraMap ℚ (AlgebraicClosure ℚ) nu))) = 5 := by
  rw [functionField_eq]
  let K := AlgebraicClosure ℚ
  let E := OppositeNormalizedField.field (algebraMap ℚ K mu) (algebraMap ℚ K nu)
  let : IsCurveOver K E := RatFuncFiniteExtension.isCurveOver_of_charZero K E
  let : Algebra.EssFiniteType K E := RatFuncFiniteExtension.essFiniteType K E
  obtain ⟨hf, hg⟩ := finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed (K := K) (F := E)
  exact ⟨hf, hg.trans (OppositeGenus.geometric_genusFF_eq_five mu nu hnu hpos hlt)⟩

#print axioms rational_regularDiffs_finrank_five
end FourCorner.OppositeAffineModel
