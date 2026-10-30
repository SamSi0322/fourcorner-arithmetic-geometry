import ThetaCoverClassPortable.ThetaSourceGenus
import ThetaCoverClassPortable.ThetaRationalPicardInput
import Mathlib.Algebra.CharP.Algebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped TensorProduct
namespace FourCorner.OppositeUniformGeometricGenus
open OppositePolynomials OppositeCoordinateAlgebra OppositeProjective OppositeProjective.ExactGenus
variable (K : Type) [Field K] [Algebra ℚ K]

abbrev X := pullback (toBase (1:ℚ) 5) (Scheme.TwoAffineOpenCover.specMap ℚ K)
abbrev c := pullback.snd (toBase (1:ℚ) 5) (Scheme.TwoAffineOpenCover.specMap ℚ K)

/-- Actual integrality of this particular categorical pullback over ANY K. -/
theorem integral : IsIntegral (X K) := by
  letI := PostIntegral.rational_literal_projective_integral (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  haveI := cover0_nonempty (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  haveI := cover1_nonempty (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  haveI := cover01_nonempty (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  exact SchemeFieldBaseChange.isIntegral_pullback (toBase (1:ℚ) 5) (V (1:ℚ) 5) K
    (field_tensor_domain (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num) K)

/-- This extends the old Qbar-only presentation by assembling the EXISTING
arbitrary-K tensor and native base-change comparisons, not by specializing a
Qbar genus result to K. -/
def literalFieldEquiv :
    letI := integral K
    letI := (baseToFunctionField (c K)).toAlgebra
    letI := OppositeAffineModel.rational_all_field_extensions_integral K (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
    FractionRing (K ⊗[ℚ] ring (1:ℚ) 5) ≃ₐ[K] (X K).functionField := by
  letI := PostIntegral.rational_literal_projective_integral (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  letI := SchemeFieldBaseChange.fieldAlgebra (toBase (1:ℚ) 5)
  letI := integral K
  letI := (baseToFunctionField (c K)).toAlgebra
  letI := OppositeAffineModel.rational_all_field_extensions_integral K (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  letI := OppositeAffineModel.rational_functionField_all_extensions_domain K (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  letI := field_tensor_domain (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num) K
  haveI := cover0_nonempty (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  haveI := cover1_nonempty (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  haveI := cover01_nonempty (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  let eT : (K ⊗[ℚ] functionField (1:ℚ) 5) ≃ₐ[K]
      (K ⊗[ℚ] (curve (1:ℚ) 5).functionField) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
      (fieldEquivAlg (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num))
  let e1 : FractionRing (K ⊗[ℚ] functionField (1:ℚ) 5) ≃ₐ[K]
      FractionRing (K ⊗[ℚ] (curve (1:ℚ) 5).functionField) :=
    IsFractionRing.algEquivOfAlgEquiv eT
  exact (HighGenus.tensorLiteralFractionEquiv (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num) K).trans
    (e1.trans (SchemeFieldBaseChange.pullbackFunctionFieldEquiv (toBase (1:ℚ) 5) (V (1:ℚ) 5)
      K (field_tensor_domain (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num) K)))

/-- Uniform genus FIVE of the ACTUAL K-pullback, for EVERY algebraically
closed extension field K of Q; all field/model identifications are proved. -/
theorem genus_five [IsAlgClosed K] :
    letI := integral K
    letI := (baseToFunctionField (c K)).toAlgebra
    genusFF K (X K).functionField=5 := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI := integral K
  letI := (baseToFunctionField (c K)).toAlgebra
  letI := OppositeAffineModel.rational_all_field_extensions_integral K (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num)
  exact (genusFF_eq_of_algEquiv (literalFieldEquiv K)).symm.trans
    (OppositeGeometricAffine.tensor_fraction_genus (L:=K) (by norm_num : (1:ℚ)≠0) (by norm_num : (5:ℚ)≠0)
      (rational_A_ne_zero (1:ℚ) 5 (by norm_num))
      (rational_B_ne_zero (1:ℚ) 5 (by norm_num) (by norm_num) (by norm_num))
      (rational_S_ne_zero (1:ℚ) 5 (by norm_num)))

#print axioms literalFieldEquiv
#print axioms genus_five
end FourCorner.OppositeUniformGeometricGenus
