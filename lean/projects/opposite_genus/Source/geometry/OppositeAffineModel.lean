import geometry.OppositeCoordinateAlgebra
import geometry.OppositeLiteralPresentation
import geometry.MultiquadraticCoordinateUniversal

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open Polynomial AlgebraicCurve
open scoped TensorProduct
namespace FourCorner.OppositeAffineModel
open OppositePolynomials OppositeCoordinatePolynomials OppositeCoordinateAlgebra

variable {K : Type*} [Field K] [CharZero K]

abbrev coordinateP (mu nu : K) := Multiquadratic.CoordinateAlgebra.coordinate₁ K[X]
  (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2)
abbrev coordinateQ (mu nu : K) := Multiquadratic.CoordinateAlgebra.coordinate₂ K[X]
  (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2)
abbrev coordinateR (mu nu : K) := Multiquadratic.CoordinateAlgebra.coordinate₃ K[X]
  (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2)

/-- Every solution of the original three equations over an arbitrary K-algebra
has one and only one coordinate-ring map with the prescribed parameter and
ordered coordinates. -/
theorem existsUnique_original_lift {T : Type*} [CommRing T] [Algebra K T]
    (mu nu : K) (hA : A mu nu ≠ 0) (z p q r : T)
    (h : z^2 = algebraMap K T (A mu nu) * (p^2 - 2*(algebraMap K T nu)^2) ∧
      q^2 = p^2 + (algebraMap K T mu)^2 + 2*z ∧
      r^2 = p^2 + (algebraMap K T mu)^2 - 2*z) :
    ∃! f : ring mu nu →+* T,
      (∀ u : K[X], f (algebraMap K[X] (ring mu nu) u) = aeval z u) ∧
      f (coordinateP mu nu) = p ∧ f (coordinateQ mu nu) = q ∧ f (coordinateR mu nu) = r := by
  obtain ⟨hp, hq, hr⟩ := (OppositeLiteralPresentation.equations_iff mu nu hA z p q r).mp h
  exact Multiquadratic.CoordinateUniversal.existsUnique_lift K[X] T (aeval z).toRingHom
    (coefficient mu nu 0) (coefficient mu nu 1) (coefficient mu nu 2) p q r hp hq hr

/-- Conversely every coordinate-ring map gives a solution of all the original
relations. Together with uniqueness this identifies the literal presentation. -/
theorem original_equations_of_hom {T : Type*} [CommRing T] [Algebra K T]
    (mu nu : K) (hA : A mu nu ≠ 0) (z : T) (f : ring mu nu →+* T)
    (hbase : ∀ u : K[X], f (algebraMap K[X] (ring mu nu) u) = aeval z u) :
    z^2 = algebraMap K T (A mu nu) * ((f (coordinateP mu nu))^2 - 2*(algebraMap K T nu)^2) ∧
      (f (coordinateQ mu nu))^2 = (f (coordinateP mu nu))^2 + (algebraMap K T mu)^2 + 2*z ∧
      (f (coordinateR mu nu))^2 = (f (coordinateP mu nu))^2 + (algebraMap K T mu)^2 - 2*z := by
  apply (OppositeLiteralPresentation.equations_iff mu nu hA z _ _ _).mpr
  constructor
  · rw [← map_pow, Multiquadratic.CoordinateAlgebra.coordinate₁_sq, hbase]
  constructor
  · rw [← map_pow, Multiquadratic.CoordinateAlgebra.coordinate₂_sq, hbase]
  · rw [← map_pow, Multiquadratic.CoordinateAlgebra.coordinate₃_sq, hbase]

/-- The genus computation is attached to the actual fraction field of the
literal coordinate ring. -/
theorem genus_actual_fractionField [IsAlgClosed K] {mu nu : K}
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (hA : A mu nu ≠ 0)
    (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    genusFF K (functionField mu nu) = 5 := by
  rw [functionField_eq]
  exact OppositeGenus.genusFF_eq_five hmu hnu hA hB hS

/-- The affine coordinate ring over Q is integral for every rational parameter
in the opposite-pair range. -/
theorem rational_coordinateRing_isDomain (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) : IsDomain (ring mu nu) := by
  have hmu : mu ≠ 0 := by intro hz; simp [hz] at hpos
  exact coordinateRing_isDomain hmu hnu (rational_A_ne_zero mu nu hnu)
    (rational_B_ne_zero mu nu hnu hpos hlt) (rational_S_ne_zero mu nu hnu)

/-- The exact radical construction over Q is the fraction field of the
literal affine coordinate algebra. -/
theorem rational_coordinateRing_isFractionRing (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) : IsFractionRing (ring mu nu) (functionField mu nu) := by
  have hmu : mu ≠ 0 := by intro hz; simp [hz] at hpos
  exact coordinateRing_isFractionRing hmu hnu (rational_A_ne_zero mu nu hnu)
    (rational_B_ne_zero mu nu hnu hpos hlt) (rational_S_ne_zero mu nu hnu)

/-- Geometric integrality in its scalar-extension coordinate-ring form:
every extension field of Q has a domain as the tensor-product coordinate ring. -/
theorem rational_all_field_extensions_integral (L : Type*) [Field L] [Algebra ℚ L]
    (mu nu : ℚ) (hnu : nu ≠ 0) (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    IsDomain (L ⊗[ℚ] ring mu nu) := by
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hmu : mu ≠ 0 := by intro hz; simp [hz] at hpos
  exact baseChange_isDomain (L := L) hmu hnu (rational_A_ne_zero mu nu hnu)
    (rational_B_ne_zero mu nu hnu hpos hlt) (rational_S_ne_zero mu nu hnu)

/-- The genuine fraction field of the scalar-extended literal coordinate ring
has genus five over Qbar. -/
theorem rational_geometric_genus_five (mu nu : ℚ) (hnu : nu ≠ 0)
    (hpos : 0 < mu / nu) (hlt : mu / nu < 2) :
    genusFF (AlgebraicClosure ℚ)
      (functionField (algebraMap ℚ (AlgebraicClosure ℚ) mu)
        (algebraMap ℚ (AlgebraicClosure ℚ) nu)) = 5 := by
  rw [functionField_eq]
  exact OppositeGenus.geometric_genusFF_eq_five mu nu hnu hpos hlt

#print axioms existsUnique_original_lift
#print axioms original_equations_of_hom
#print axioms genus_actual_fractionField
#print axioms rational_coordinateRing_isDomain
#print axioms rational_coordinateRing_isFractionRing
#print axioms rational_all_field_extensions_integral
#print axioms rational_geometric_genus_five
end FourCorner.OppositeAffineModel
