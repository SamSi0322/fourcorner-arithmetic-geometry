import ThetaCoverClassPortable.geometry.MultiquadraticCoordinateAlgebra
import ThetaCoverClassPortable.geometry.OppositeCoordinatePolynomials
import ThetaCoverClassPortable.geometry.PolynomialCoordinateBaseChange
import ThetaCoverClassPortable.geometry.OppositeGenus

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
open scoped TensorProduct
namespace FourCorner.OppositeCoordinateAlgebra
open OppositePolynomials OppositeCoordinatePolynomials

variable {K : Type*} [Field K] [CharZero K]

/-- The actual affine coordinate ring, formed by the three successive monic
quadratic quotients over K[Z]. -/
abbrev ring (mu nu : K) :=
  Multiquadratic.CoordinateAlgebra.Stage₃ K[X] (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2)

/-- The explicit field into which all three coordinate quotients embed. -/
abbrev functionField (mu nu : K) :=
  Multiquadratic.CoordinateAlgebra.field₃ K[X] (RatFunc K) (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2)

theorem functionField_eq (mu nu : K) :
    functionField mu nu = OppositeNormalizedField.field mu nu := by
  change Multiquadratic.field (RatFunc K)
    (algebraMap K[X] (RatFunc K) (coefficient mu nu 0))
    (algebraMap K[X] (RatFunc K) (coefficient mu nu 1))
    (algebraMap K[X] (RatFunc K) (coefficient mu nu 2)) = _
  rw [map_coefficient, map_coefficient, map_coefficient]

theorem independence {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    Multiquadratic.IndependentSquareclasses (RatFunc K)
      (algebraMap K[X] (RatFunc K) (coefficient mu nu 0))
      (algebraMap K[X] (RatFunc K) (coefficient mu nu 1))
      (algebraMap K[X] (RatFunc K) (coefficient mu nu 2)) :=
  Multiquadratic.independentSquareclasses_of_products (RatFunc K)
    (fun i => algebraMap K[X] (RatFunc K) (coefficient mu nu i))
    (OppositeCoordinatePolynomials.nonempty_product_nonsquare hmu hnu hA hB hS)

/-- Injectivity is proved from the actual seven nonsquare products. -/
theorem embedding_injective {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    Function.Injective (Multiquadratic.CoordinateAlgebra.map₃ K[X] (RatFunc K)
      (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2)) :=
  Multiquadratic.CoordinateAlgebra.map₃_injective K[X] (RatFunc K) _ _ _ (IsFractionRing.injective _ _) (by norm_num)
    (independence hmu hnu hA hB hS)

/-- The literal affine coordinate ring is a domain. -/
theorem coordinateRing_isDomain {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsDomain (ring mu nu) :=
  Multiquadratic.CoordinateAlgebra.stage₃_isDomain K[X] (RatFunc K) _ _ _ (IsFractionRing.injective _ _) (by norm_num)
    (independence hmu hnu hA hB hS)

/-- The constructed radical field is genuinely the fraction field of the
literal coordinate ring. -/
theorem coordinateRing_isFractionRing {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsFractionRing (ring mu nu) (functionField mu nu) :=
  Multiquadratic.CoordinateAlgebra.isFractionRing_stage₃ K[X] (RatFunc K) _ _ _ (by norm_num)
    (independence hmu hnu hA hB hS)

/-- Scalar extension is the actual tensor-product coordinate ring with mapped
coefficients, not merely a second independently constructed model. -/
def baseChangeEquiv {L : Type*} [Field L] [CharZero L] [Algebra K L] (mu nu : K) :
    L ⊗[K] ring mu nu ≃ₐ[L] ring (algebraMap K L mu) (algebraMap K L nu) := by
  exact Multiquadratic.BaseChange.stage₃EquivOfImages (polyEquivTensor' K L).symm
    (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2)
    (coefficient (algebraMap K L mu) (algebraMap K L nu) 0)
    (coefficient (algebraMap K L mu) (algebraMap K L nu) 1)
    (coefficient (algebraMap K L mu) (algebraMap K L nu) 2)
    (by simpa only [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul,
      one_smul] using coefficient_map (algebraMap K L) mu nu (0 : Fin 3))
    (by simpa only [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul,
      one_smul] using coefficient_map (algebraMap K L) mu nu (1 : Fin 3))
    (by simpa only [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul,
      one_smul] using coefficient_map (algebraMap K L) mu nu (2 : Fin 3))

/-- All extensions of the constant field preserve integrality of the literal
polynomial source. -/
theorem baseChange_isDomain {L : Type*} [Field L] [CharZero L] [Algebra K L]
    {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    IsDomain (L ⊗[K] ring mu nu) := by
  have hmu' := (_root_.map_ne_zero (algebraMap K L)).2 hmu
  have hnu' := (_root_.map_ne_zero (algebraMap K L)).2 hnu
  have hA' : A (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [A_map] using (_root_.map_ne_zero (algebraMap K L)).2 hA
  have hB' : B (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [B_map] using (_root_.map_ne_zero (algebraMap K L)).2 hB
  have hS' : S (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [S_map] using (_root_.map_ne_zero (algebraMap K L)).2 hS
  let := coordinateRing_isDomain hmu' hnu' hA' hB' hS'
  exact Function.Injective.isDomain (baseChangeEquiv mu nu).toRingHom
    (baseChangeEquiv mu nu).injective

#print axioms functionField_eq
#print axioms embedding_injective
#print axioms coordinateRing_isDomain
#print axioms coordinateRing_isFractionRing
#print axioms baseChangeEquiv
#print axioms baseChange_isDomain
end FourCorner.OppositeCoordinateAlgebra
