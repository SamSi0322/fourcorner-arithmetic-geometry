import ThetaCoverClassPortable.geometry.AdjacentConicNonsquare
import ThetaCoverClassPortable.geometry.AdjacentConicTranscendence
import ThetaCoverClassPortable.geometry.AdjoinRootInjective
import ThetaCoverClassPortable.geometry.GeneratedFractionField
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Literal quadratic coordinate quotients and their generated function fields

The source ring is a polynomial quotient by the equation, rather than a subring
chosen in the target. Injectivity is derived from the nonsquare generic radicand.
-/

noncomputable section

namespace FourCorner.AdjacentConicQuotient

open Polynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

def quadraticEquation (d : K[X]) : K[X][X] := X ^ 2 - C d

abbrev QuadraticCoordinateRing (d : K[X]) := AdjoinRoot (quadraticEquation d)

def coordinateU (d : K[X]) : QuadraticCoordinateRing d :=
  algebraMap K[X] (QuadraticCoordinateRing d) X

def coordinateV (d : K[X]) : QuadraticCoordinateRing d :=
  AdjoinRoot.root (quadraticEquation d)

theorem quadraticEquation_monic (d : K[X]) : (quadraticEquation d).Monic :=
  monic_X_pow_sub_C d (by decide)

theorem coordinate_relation (d : K[X]) :
    coordinateV d ^ 2 = aeval (coordinateU d) d := by
  have h := AdjoinRoot.eval₂_root (quadraticEquation d)
  change (X ^ 2 - C d : K[X][X]).eval₂ (AdjoinRoot.of (quadraticEquation d))
    (AdjoinRoot.root (quadraticEquation d)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  rw [coordinateV, h]
  change algebraMap K[X] (QuadraticCoordinateRing d) d = _
  have he : aeval (coordinateU d) =
      IsScalarTower.toAlgHom K K[X] (QuadraticCoordinateRing d) := by
    ext
    simp [coordinateU]
  rw [he]
  rfl

theorem evaluation_root (d : K[X]) (u v : E) (h : v ^ 2 = aeval u d) :
    (quadraticEquation d).eval₂ (aeval u).toRingHom v = 0 := by
  simp only [quadraticEquation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  exact sub_eq_zero.mpr h

/-- The quotient map sends the two literal coordinates to the specified point. -/
def evaluation (d : K[X]) (u v : E) (h : v ^ 2 = aeval u d) :
    QuadraticCoordinateRing d →ₐ[K] E :=
  AdjoinRoot.liftAlgHom (quadraticEquation d) (aeval u) v (evaluation_root d u v h)

@[simp] theorem evaluation_U (d : K[X]) (u v : E) (h : v ^ 2 = aeval u d) :
    evaluation d u v h (coordinateU d) = u := by
  change AdjoinRoot.lift (aeval u).toRingHom v (evaluation_root d u v h)
    (AdjoinRoot.of (quadraticEquation d) X) = u
  rw [AdjoinRoot.lift_of]
  exact aeval_X u

@[simp] theorem evaluation_V (d : K[X]) (u v : E) (h : v ^ 2 = aeval u d) :
    evaluation d u v h (coordinateV d) = v := by
  exact AdjoinRoot.lift_root (evaluation_root d u v h)

/-- A nonsquare generic equation and a transcendental first coordinate force
injectivity of the literal coordinate quotient map. -/
theorem evaluation_injective (d : K[X]) (u v : E)
    (h : v ^ 2 = aeval u d) (hu : Transcendental K u)
    (hd : ¬ IsSquare (algebraMap K[X] (RatFunc K) d)) :
    Function.Injective (evaluation d u v h) := by
  let i : K[X] →+* RatFunc K := algebraMap K[X] (RatFunc K)
  let j : RatFunc K →+* E := IsFractionRing.lift (transcendental_iff_injective.mp hu)
  have hji : j.comp i = (aeval u).toRingHom := by
    apply RingHom.ext
    intro p
    exact IsFractionRing.lift_algebraMap (K := RatFunc K)
      (g := (aeval u).toRingHom) (transcendental_iff_injective.mp hu) p
  have hirr : Irreducible ((quadraticEquation d).map i) := by
    simp only [quadraticEquation, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    intro z hz
    exact hd ⟨z, by simpa only [sq] using hz.symm⟩
  have hr : (quadraticEquation d).eval₂ (j.comp i) v = 0 := by
    rw [hji]
    exact evaluation_root d u v h
  have hi := AdjoinRootInjective.lift_injective_of_monic_of_irreducible_map
    i (IsFractionRing.injective K[X] (RatFunc K)) (quadraticEquation d)
    (quadraticEquation_monic d) j v hirr hr
  change Function.Injective (AdjoinRoot.lift (f := quadraticEquation d)
    (aeval (R := K) u).toRingHom v (evaluation_root d u v h))
  simpa only [hji] using hi

/-- The coordinate quotient is a domain whenever its generic radicand is nonsquare. -/
theorem coordinateRing_isDomain (d : K[X])
    (hd : ¬ IsSquare (algebraMap K[X] (RatFunc K) d)) :
    IsDomain (QuadraticCoordinateRing d) := by
  have hirr : Irreducible ((quadraticEquation d).map (algebraMap K[X] (RatFunc K))) := by
    simp only [quadraticEquation, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    intro z hz
    exact hd ⟨z, by simpa only [sq] using hz.symm⟩
  letI : Fact (Irreducible ((quadraticEquation d).map (algebraMap K[X] (RatFunc K)))) :=
    ⟨hirr⟩
  exact Function.Injective.isDomain
    (AdjoinRoot.map (algebraMap K[X] (RatFunc K)) _ _ dvd_rfl)
    (AdjoinRootInjective.map_injective _ (IsFractionRing.injective K[X] (RatFunc K))
      _ (quadraticEquation_monic d))

/-- Field generation establishes the actual fraction-field structure. -/
theorem evaluation_isFractionRing (d : K[X]) (u v : E)
    (h : v ^ 2 = aeval u d) (hu : Transcendental K u)
    (hd : ¬ IsSquare (algebraMap K[X] (RatFunc K) d))
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) :
    letI : Algebra (QuadraticCoordinateRing d) E := (evaluation d u v h).toRingHom.toAlgebra
    IsFractionRing (QuadraticCoordinateRing d) E := by
  letI : Algebra (QuadraticCoordinateRing d) E := (evaluation d u v h).toRingHom.toAlgebra
  letI : IsDomain (QuadraticCoordinateRing d) := coordinateRing_isDomain d hd
  letI : IsScalarTower K (QuadraticCoordinateRing d) E :=
    IsScalarTower.of_algebraMap_eq fun x => ((evaluation d u v h).commutes x).symm
  apply GeneratedFractionField.isFractionRing_of_adjoin_eq_top K
    (QuadraticCoordinateRing d) K E (evaluation_injective d u v h hu hd) {u, v}
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨coordinateU d, (evaluation_U d u v h).trans hx.symm⟩
    · exact ⟨coordinateV d, (evaluation_V d u v h).trans hx.symm⟩
  · exact hgen

/-- The function field of the literal quotient is identified with the field
generated by its two coordinate images. -/
def evaluationFractionEquiv (d : K[X]) (u v : E)
    (h : v ^ 2 = aeval u d) (hu : Transcendental K u)
    (hd : ¬ IsSquare (algebraMap K[X] (RatFunc K) d))
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) :
    FractionRing (QuadraticCoordinateRing d) ≃ₐ[K] E := by
  letI : Algebra (QuadraticCoordinateRing d) E := (evaluation d u v h).toRingHom.toAlgebra
  letI : IsDomain (QuadraticCoordinateRing d) := coordinateRing_isDomain d hd
  letI : IsScalarTower K (QuadraticCoordinateRing d) E :=
    IsScalarTower.of_algebraMap_eq fun x => ((evaluation d u v h).commutes x).symm
  letI := evaluation_isFractionRing d u v h hu hd hgen
  exact (FractionRing.algEquiv (QuadraticCoordinateRing d) E).restrictScalars K

@[simp] theorem evaluationFractionEquiv_algebraMap (d : K[X]) (u v : E)
    (h : v ^ 2 = aeval u d) (hu : Transcendental K u)
    (hd : ¬ IsSquare (algebraMap K[X] (RatFunc K) d))
    (hgen : IntermediateField.adjoin K {u, v} = ⊤) (x : QuadraticCoordinateRing d) :
    evaluationFractionEquiv d u v h hu hd hgen
      (algebraMap (QuadraticCoordinateRing d) (FractionRing (QuadraticCoordinateRing d)) x) =
      evaluation d u v h x := by
  letI : Algebra (QuadraticCoordinateRing d) E := (evaluation d u v h).toRingHom.toAlgebra
  letI : IsDomain (QuadraticCoordinateRing d) := coordinateRing_isDomain d hd
  letI : IsScalarTower K (QuadraticCoordinateRing d) E :=
    IsScalarTower.of_algebraMap_eq fun x => ((evaluation d u v h).commutes x).symm
  letI := evaluation_isFractionRing d u v h hu hd hgen
  exact (FractionRing.algEquiv (QuadraticCoordinateRing d) E).commutes x

section Conic

variable [CharZero K]

/-- The normalized literal adjacent-conic coordinate ring. -/
abbrev CoordinateRing (c : K) := QuadraticCoordinateRing (radicand c (c ^ 2 - 1))

theorem normalized_relation (c : K) (hc : c ≠ 0) :
    AdjacentConic.v c ^ 2 = aeval (AdjacentConic.u c) (radicand c (c ^ 2 - 1)) := by
  have h := AdjacentConic.conic_identity c hc
  have hcE : algebraMap K (RatFunc K) c ≠ 0 := (map_ne_zero (algebraMap K (RatFunc K))).2 hc
  simp only [radicand, map_sub, map_mul, map_pow, aeval_C, aeval_X, map_div₀, map_one]
  field_simp
  linear_combination h

/-- The explicit rational parametrization descends from the polynomial quotient. -/
def parametrization (c : K) (hc : c ≠ 0) : CoordinateRing c →ₐ[K] RatFunc K :=
  evaluation (radicand c (c ^ 2 - 1)) (AdjacentConic.u c) (AdjacentConic.v c)
    (normalized_relation c hc)

@[simp] theorem parametrization_U (c : K) (hc : c ≠ 0) :
    parametrization c hc (coordinateU (radicand c (c ^ 2 - 1))) = AdjacentConic.u c :=
  evaluation_U _ _ _ _

@[simp] theorem parametrization_V (c : K) (hc : c ≠ 0) :
    parametrization c hc (coordinateV (radicand c (c ^ 2 - 1))) = AdjacentConic.v c :=
  evaluation_V _ _ _ _

/-- The rational parametrization embeds the actual conic quotient. -/
theorem parametrization_injective (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    Function.Injective (parametrization c hc) :=
  evaluation_injective _ _ _ _ (AdjacentConic.u_transcendental c hc hA)
    (radicand_not_isSquare c _ hc hA)

theorem conicCoordinateRing_isDomain (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    IsDomain (CoordinateRing c) :=
  coordinateRing_isDomain _ (radicand_not_isSquare c _ hc hA)

/-- The actual fraction field of the polynomial quotient is `K(t)`. -/
def functionFieldEquiv (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    FractionRing (CoordinateRing c) ≃ₐ[K] RatFunc K :=
  evaluationFractionEquiv _ _ _ (normalized_relation c hc)
    (AdjacentConic.u_transcendental c hc hA) (radicand_not_isSquare c _ hc hA)
    (AdjacentConic.coordinates_generate c hc hA)

@[simp] theorem functionFieldEquiv_algebraMap (c : K) (hc : c ≠ 0)
    (hA : c ^ 2 - 1 ≠ 0) (x : CoordinateRing c) :
    functionFieldEquiv c hc hA (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) x) =
      parametrization c hc x :=
  evaluationFractionEquiv_algebraMap _ _ _ _ _ _ _ x

@[simp] theorem functionFieldEquiv_U (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    functionFieldEquiv c hc hA (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c))
      (coordinateU (radicand c (c ^ 2 - 1)))) = AdjacentConic.u c := by
  rw [functionFieldEquiv_algebraMap, parametrization_U]

@[simp] theorem functionFieldEquiv_V (c : K) (hc : c ≠ 0) (hA : c ^ 2 - 1 ≠ 0) :
    functionFieldEquiv c hc hA (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c))
      (coordinateV (radicand c (c ^ 2 - 1)))) = AdjacentConic.v c := by
  rw [functionFieldEquiv_algebraMap, parametrization_V]

end Conic

end FourCorner.AdjacentConicQuotient

#print axioms FourCorner.AdjacentConicQuotient.evaluation_injective
#print axioms FourCorner.AdjacentConicQuotient.evaluationFractionEquiv

#print axioms FourCorner.AdjacentConicQuotient.parametrization_injective
#print axioms FourCorner.AdjacentConicQuotient.functionFieldEquiv
#print axioms FourCorner.AdjacentConicQuotient.functionFieldEquiv_U
#print axioms FourCorner.AdjacentConicQuotient.functionFieldEquiv_V
