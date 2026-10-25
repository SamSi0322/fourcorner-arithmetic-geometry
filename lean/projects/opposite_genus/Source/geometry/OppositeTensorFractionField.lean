import geometry.OppositeAffineModel

noncomputable section
open scoped TensorProduct
namespace FourCorner.OppositeCoordinateAlgebra
open OppositePolynomials
variable {K : Type*} [Field K] [CharZero K]
variable {L : Type*} [Field L] [CharZero L] [Algebra K L]

/-- The structural map from the genuine tensor product to its mapped-coefficient
radical field. -/
abbrev tensorFractionAlgebra (mu nu : K) :
    Algebra (L ⊗[K] ring mu nu)
      (functionField (algebraMap K L mu) (algebraMap K L nu)) :=
  ((algebraMap (ring (algebraMap K L mu) (algebraMap K L nu))
      (functionField (algebraMap K L mu) (algebraMap K L nu))).comp
    (baseChangeEquiv (L := L) mu nu).toRingHom).toAlgebra

/-- Fraction-field identification directly on the actual tensor-product ring. -/
theorem tensor_isFractionRing {mu nu : K} (hmu : mu ≠ 0) (hnu : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    let := tensorFractionAlgebra (L := L) mu nu
    IsFractionRing (L ⊗[K] ring mu nu)
      (functionField (algebraMap K L mu) (algebraMap K L nu)) := by
  let := tensorFractionAlgebra (L := L) mu nu
  have hmu' := (_root_.map_ne_zero (algebraMap K L)).2 hmu
  have hnu' := (_root_.map_ne_zero (algebraMap K L)).2 hnu
  have hA' : A (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [A_map] using (_root_.map_ne_zero (algebraMap K L)).2 hA
  have hB' : B (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [B_map] using (_root_.map_ne_zero (algebraMap K L)).2 hB
  have hS' : S (algebraMap K L mu) (algebraMap K L nu) ≠ 0 := by
    simpa only [S_map] using (_root_.map_ne_zero (algebraMap K L)).2 hS
  let := coordinateRing_isFractionRing hmu' hnu' hA' hB' hS'
  exact IsFractionRing.of_ringEquiv_left (baseChangeEquiv (L := L) mu nu).toRingEquiv
    (fun _ => rfl)

/-- Concrete Qbar tensor statement, with only the paper's rational range. -/
theorem rational_geometric_tensor_isFractionRing (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    letI := tensorFractionAlgebra (L := AlgebraicClosure ℚ) mu nu
    IsFractionRing ((AlgebraicClosure ℚ) ⊗[ℚ] ring mu nu)
      (functionField (algebraMap ℚ (AlgebraicClosure ℚ) mu)
        (algebraMap ℚ (AlgebraicClosure ℚ) nu)) := by
  have hmu : mu ≠ 0 := by intro hz; simp [hz] at hpos
  exact tensor_isFractionRing hmu hnu (rational_A_ne_zero mu nu hnu)
    (rational_B_ne_zero mu nu hnu hpos hlt) (rational_S_ne_zero mu nu hnu)

#print axioms tensor_isFractionRing
#print axioms rational_geometric_tensor_isFractionRing
end FourCorner.OppositeCoordinateAlgebra
