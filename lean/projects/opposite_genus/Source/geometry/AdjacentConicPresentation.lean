import geometry.AdjacentConicQuotient
import geometry.AdjacentConicNonsquare

/-!
The literal adjacent conic equation `A U² + c² V² - c² A` defines the same
coordinate ring as the monic quadratic equation `V² - (A - A / c² * U²)`
when `c ≠ 0`. The equivalence comes from multiplication by the unit `c²`
and preserves both polynomial coordinates and all coefficients.
-/

noncomputable section

namespace FourCorner.AdjacentConicPresentation

open Polynomial AdjacentConicQuotient

variable {K : Type*} [Field K]

/-- The unnormalized conic equation, with inner variable `U` and outer variable `V`. -/
def literalEquation (c A : K) : K[X][X] :=
  C (C A * X ^ 2) + C (C (c ^ 2)) * X ^ 2 - C (C (c ^ 2 * A))

/-- Dividing the literal equation by `c²` yields the normalized quadratic. -/
theorem literalEquation_factor (c A : K) (hc : c ≠ 0) :
    literalEquation c A = C (C (c ^ 2)) * quadraticEquation (radicand c A) := by
  have hcc : c ^ 2 * (A / c ^ 2) = A := by field_simp
  have hcoeff : C (C (c ^ 2)) * C (C (A / c ^ 2)) = (C (C A) : K[X][X]) := by
    rw [← map_mul, ← map_mul, hcc]
  simp only [map_pow] at hcoeff
  simp only [literalEquation, quadraticEquation, radicand, map_sub, map_mul, map_pow]
  linear_combination -(C (X : K[X])) ^ 2 * hcoeff

/-- The two defining equations differ by a unit in the actual polynomial ring. -/
theorem literalEquation_associated (c A : K) (hc : c ≠ 0) :
    Associated (literalEquation c A) (quadraticEquation (radicand c A)) := by
  rw [literalEquation_factor c A hc]
  apply associated_unit_mul_left
  exact isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hc)))

/-- The literal quotient `K[U][V] / (A U² + c² V² - c² A)`. -/
abbrev LiteralCoordinateRing (c A : K) := AdjoinRoot (literalEquation c A)

def coordinateU (c A : K) : LiteralCoordinateRing c A :=
  algebraMap K[X] (LiteralCoordinateRing c A) X

def coordinateV (c A : K) : LiteralCoordinateRing c A :=
  AdjoinRoot.root (literalEquation c A)

/-- The canonical equivalence obtained from the unit multiple of the defining equation. -/
def normalizeEquiv (c A : K) (hc : c ≠ 0) :
    LiteralCoordinateRing c A ≃ₐ[K] QuadraticCoordinateRing (radicand c A) :=
  AdjoinRoot.algEquivOfAssociated K _ _ (literalEquation_associated c A hc)

@[simp] theorem normalizeEquiv_coefficient (c A : K) (hc : c ≠ 0) (p : K[X]) :
    normalizeEquiv c A hc (algebraMap K[X] (LiteralCoordinateRing c A) p) =
      algebraMap K[X] (QuadraticCoordinateRing (radicand c A)) p := by
  simp [normalizeEquiv, AdjoinRoot.algEquivOfAssociated, AdjoinRoot.mapAlgEquiv,
    AdjoinRoot.mapAlgHom, AdjoinRoot.algebraMap_eq]

@[simp] theorem normalizeEquiv_U (c A : K) (hc : c ≠ 0) :
    normalizeEquiv c A hc (coordinateU c A) = AdjacentConicQuotient.coordinateU (radicand c A) :=
  normalizeEquiv_coefficient c A hc X

@[simp] theorem normalizeEquiv_V (c A : K) (hc : c ≠ 0) :
    normalizeEquiv c A hc (coordinateV c A) = AdjacentConicQuotient.coordinateV (radicand c A) := by
  exact AdjoinRoot.algEquivOfAssociated_root _ _ _

#print axioms literalEquation_factor
#print axioms normalizeEquiv
#print axioms normalizeEquiv_coefficient
#print axioms normalizeEquiv_U
#print axioms normalizeEquiv_V

end FourCorner.AdjacentConicPresentation
