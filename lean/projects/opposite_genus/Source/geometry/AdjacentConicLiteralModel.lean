import geometry.AdjacentConicPresentation
import geometry.AdjacentConicOpenChart
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
The actual literal adjacent-conic quotient, its injective parametrization,
and the induced identification of its fraction field with `K(t)`.
The source is `K[U][V] / ((c²-1)U²+c²V²-c²(c²-1))`.
-/

noncomputable section
namespace FourCorner.AdjacentConicLiteralModel

variable {K : Type*} [Field K] [CharZero K]

abbrev CoordinateRing (c : K) :=
  AdjacentConicPresentation.LiteralCoordinateRing c (c ^ 2 - 1)

def coordinateU (c : K) : CoordinateRing c :=
  AdjacentConicPresentation.coordinateU c (c ^ 2 - 1)

def coordinateV (c : K) : CoordinateRing c :=
  AdjacentConicPresentation.coordinateV c (c ^ 2 - 1)

/-- The displayed parametrization descends from the original conic equation. -/
def parametrization (c : K) (hc : c ≠ 0) : CoordinateRing c →ₐ[K] RatFunc K :=
  (AdjacentConicQuotient.parametrization c hc).comp
    (AdjacentConicPresentation.normalizeEquiv c (c ^ 2 - 1) hc).toAlgHom

@[simp] theorem parametrization_U (c : K) (hc : c ≠ 0) :
    parametrization c hc (coordinateU c) = AdjacentConic.u c := by
  simp [parametrization, coordinateU]

@[simp] theorem parametrization_V (c : K) (hc : c ≠ 0) :
    parametrization c hc (coordinateV c) = AdjacentConic.v c := by
  simp [parametrization, coordinateV]

/-- No component or additional relation is lost by the parametrization. -/
theorem parametrization_injective (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    Function.Injective (parametrization c hc) :=
  (AdjacentConicQuotient.parametrization_injective c hc hA).comp
    (AdjacentConicPresentation.normalizeEquiv c (c ^ 2 - 1) hc).injective

theorem coordinateRing_isDomain (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    IsDomain (CoordinateRing c) :=
  Function.Injective.isDomain (parametrization c hc) (parametrization_injective c hc hA)

/-- The function field of the literal conic is the rational parameter field. -/
def functionFieldEquiv (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    FractionRing (CoordinateRing c) ≃ₐ[K] RatFunc K :=
  (IsFractionRing.algEquivOfAlgEquiv
    (K := FractionRing (CoordinateRing c))
    (L := FractionRing (AdjacentConicQuotient.CoordinateRing c))
    (AdjacentConicPresentation.normalizeEquiv c (c ^ 2 - 1) hc)).trans
      (AdjacentConicQuotient.functionFieldEquiv c hc hA)

@[simp] theorem functionFieldEquiv_algebraMap (c : K) (hc : c ≠ 0)
    (hA : c ^ 2 - 1 ≠ 0) (x : CoordinateRing c) :
    functionFieldEquiv c hc hA
        (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) x) =
      parametrization c hc x := by
  simp [functionFieldEquiv, parametrization, AlgEquiv.trans_apply]

@[simp] theorem functionFieldEquiv_U (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    functionFieldEquiv c hc hA
        (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) (coordinateU c)) =
      AdjacentConic.u c := by
  rw [functionFieldEquiv_algebraMap, parametrization_U]

@[simp] theorem functionFieldEquiv_V (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    functionFieldEquiv c hc hA
        (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) (coordinateV c)) =
      AdjacentConic.v c := by
  rw [functionFieldEquiv_algebraMap, parametrization_V]

/-- With its actual quotient map, `K(t)` is a fraction field of the literal source. -/
theorem isFractionRing (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    letI : Algebra (CoordinateRing c) (RatFunc K) :=
      (parametrization c hc).toRingHom.toAlgebra
    IsFractionRing (CoordinateRing c) (RatFunc K) := by
  letI : Algebra (CoordinateRing c) (RatFunc K) :=
    (parametrization c hc).toRingHom.toAlgebra
  exact IsFractionRing.of_algEquiv
    (AlgEquiv.ofRingEquiv (f := (functionFieldEquiv c hc hA).toRingEquiv)
      (functionFieldEquiv_algebraMap c hc hA))

/-- The stated inverse parameter is an element of the literal fraction field. -/
def slope (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    FractionRing (CoordinateRing c) := by
  letI : IsDomain (CoordinateRing c) := coordinateRing_isDomain c hc hA
  exact algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) (coordinateV c) /
    (algebraMap K (FractionRing (CoordinateRing c)) c -
      algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) (coordinateU c))

@[simp] theorem functionFieldEquiv_slope (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    functionFieldEquiv c hc hA (slope c hc hA) = RatFunc.X := by
  letI : IsDomain (CoordinateRing c) := coordinateRing_isDomain c hc hA
  simp only [slope, map_div₀, map_sub, functionFieldEquiv_U, functionFieldEquiv_V,
    AlgEquiv.commutes]
  exact AdjacentConic.inverse c hc hA

/-- The rational hypotheses in the adjacent-pair problem supply every field hypothesis. -/
def functionFieldRingEquiv (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    FractionRing (CoordinateRing c) ≃+* RatFunc K :=
  (functionFieldEquiv c hc hA).toRingEquiv

/-- The rational specialization uses the unique rational algebra structures. -/
def rationalFunctionFieldEquiv (c : ℚ) (hc : 0 < c) (hne : c ≠ 1) :
    FractionRing (CoordinateRing c) ≃ₐ[ℚ] RatFunc ℚ := by
  let e := functionFieldRingEquiv c (AdjacentConic.rational_nondegenerate c hc hne).1
    (AdjacentConic.rational_nondegenerate c hc hne).2
  exact e.toRatAlgEquiv

#print axioms parametrization_injective
#print axioms coordinateRing_isDomain
#print axioms functionFieldEquiv
#print axioms functionFieldEquiv_U
#print axioms functionFieldEquiv_V
#print axioms isFractionRing
#print axioms functionFieldEquiv_slope
#print axioms rationalFunctionFieldEquiv

end FourCorner.AdjacentConicLiteralModel
