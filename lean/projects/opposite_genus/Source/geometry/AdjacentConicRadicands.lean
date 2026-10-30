import geometry.AdjacentConicLiteralModel
import geometry.AdjacentPlaceOrders

/-!
The two ordered, literal squared-distance expressions on the adjacent conic
map to the actual rational radicands `g₂/D²` and `g₃/D²`. The map is the
previously constructed injective quotient parametrization.
-/

noncomputable section
namespace FourCorner.AdjacentConicRadicands

open Polynomial AdjacentConicLiteralModel
variable {K : Type*} [Field K] [CharZero K]

theorem u_eq_polynomial_quotient (c : K) :
    AdjacentConic.u c =
      algebraMap K[X] (RatFunc K) (AdjacentPolynomials.U c) /
        algebraMap K[X] (RatFunc K) (AdjacentPolynomials.D c) := by
  simp only [AdjacentConic.u, AdjacentConic.Chart.u, AdjacentConic.Chart.denominator,
    AdjacentPolynomials.U, AdjacentPolynomials.D, map_mul, map_pow, map_add, map_sub,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_one, RatFunc.algebraMap_eq_C]
  congr 1 <;> ring

theorem v_eq_polynomial_quotient (c : K) :
    AdjacentConic.v c =
      algebraMap K[X] (RatFunc K) (AdjacentPolynomials.V c) /
        algebraMap K[X] (RatFunc K) (AdjacentPolynomials.D c) := by
  simp only [AdjacentConic.v, AdjacentConic.Chart.v, AdjacentConic.Chart.denominator,
    AdjacentPolynomials.V, AdjacentPolynomials.D, map_mul, map_pow, map_add, map_sub,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_one, RatFunc.algebraMap_eq_C,
    map_ofNat]
  congr 1 <;> ring

theorem denominator_ne_zero (c : K) (hc : c ≠ 0) :
    algebraMap K[X] (RatFunc K) (AdjacentPolynomials.D c) ≠ 0 :=
  RatFunc.algebraMap_ne_zero (AdjacentConic.denominatorPolynomial_ne_zero c hc)

/-- The plus sign is attached to index zero and the numerator `g₂`. -/
theorem plus_identity (c : K) (hc : c ≠ 0) :
    (AdjacentConic.u c + 1) ^ 2 + (AdjacentConic.v c - 2) ^ 2 =
      AdjacentPlaceOrders.actualValue c 0 := by
  rw [u_eq_polynomial_quotient, v_eq_polynomial_quotient]
  simp only [AdjacentPlaceOrders.actualValue, AdjacentPolynomials.radicand,
    AdjacentPolynomials.g2, map_add, map_pow, map_sub, map_mul, map_ofNat]
  have hd := denominator_ne_zero c hc
  field_simp

/-- The minus sign is attached to index one and the numerator `g₃`. -/
theorem minus_identity (c : K) (hc : c ≠ 0) :
    (AdjacentConic.u c - 1) ^ 2 + (AdjacentConic.v c - 2) ^ 2 =
      AdjacentPlaceOrders.actualValue c 1 := by
  rw [u_eq_polynomial_quotient, v_eq_polynomial_quotient]
  simp only [AdjacentPlaceOrders.actualValue, AdjacentPolynomials.radicand,
    AdjacentPolynomials.g3, map_add, map_pow, map_sub, map_mul, map_ofNat]
  have hd := denominator_ne_zero c hc
  field_simp

/-- Ordered squared distances as elements of the actual literal conic quotient. -/
def radicand (c : K) : Fin 2 → CoordinateRing c
  | 0 => (coordinateU c + 1) ^ 2 + (coordinateV c - 2) ^ 2
  | 1 => (coordinateU c - 1) ^ 2 + (coordinateV c - 2) ^ 2

@[simp] theorem parametrization_radicand (c : K) (hc : c ≠ 0) (i : Fin 2) :
    parametrization c hc (radicand c i) = AdjacentPlaceOrders.actualValue c i := by
  fin_cases i
  · simpa only [radicand, map_add, map_sub, map_pow, map_one, map_ofNat,
      parametrization_U, parametrization_V, AdjacentPlaceOrders.actualValue,
      AdjacentPolynomials.radicand] using plus_identity c hc
  · simpa only [radicand, map_add, map_sub, map_pow, map_one, map_ofNat,
      parametrization_U, parametrization_V, AdjacentPlaceOrders.actualValue,
      AdjacentPolynomials.radicand] using minus_identity c hc

/-- The same ordered identities hold in the genuine fraction-field equivalence. -/
@[simp] theorem functionFieldEquiv_radicand (c : K) (hc : c ≠ 0)
    (hA : c ^ 2 - 1 ≠ 0) (i : Fin 2) :
    functionFieldEquiv c hc hA
        (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) (radicand c i)) =
      AdjacentPlaceOrders.actualValue c i := by
  rw [functionFieldEquiv_algebraMap, parametrization_radicand]

#print axioms plus_identity
#print axioms minus_identity
#print axioms parametrization_radicand
#print axioms functionFieldEquiv_radicand

end FourCorner.AdjacentConicRadicands
