import geometry.AdjacentConicRadicands
import geometry.BiquadraticCoordinateAlgebra
import geometry.AdjacentGenus

/-!
# The literal adjacent source and its actual genus-five function field

The base is the literal conic quotient. Two successive quadratic quotients
adjoin the two ordered remaining distance coordinates. The field embedding uses
the already proved conic parametrization and preserves the same base point.
-/

noncomputable section

namespace FourCorner.AdjacentCoordinateAlgebra

open AlgebraicCurve

variable {K : Type*} [Field K] [CharZero K]

/-- The literal conic with the two ordered quadratic distance equations adjoined. -/
abbrev CoordinateRing (c : K) :=
  Biquadratic.CoordinateAlgebra.CoordinateRing (AdjacentConicLiteralModel.CoordinateRing c)
    (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)

def coordinateU (c : K) : CoordinateRing c :=
  algebraMap (AdjacentConicLiteralModel.CoordinateRing c) (CoordinateRing c)
    (AdjacentConicLiteralModel.coordinateU c)

def coordinateV (c : K) : CoordinateRing c :=
  algebraMap (AdjacentConicLiteralModel.CoordinateRing c) (CoordinateRing c)
    (AdjacentConicLiteralModel.coordinateV c)

def coordinateP (c : K) : CoordinateRing c :=
  Biquadratic.CoordinateAlgebra.coordinate₁ (AdjacentConicLiteralModel.CoordinateRing c)
    (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)

def coordinateQ (c : K) : CoordinateRing c :=
  Biquadratic.CoordinateAlgebra.coordinate₂ (AdjacentConicLiteralModel.CoordinateRing c)
    (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)

omit [CharZero K] in
/-- The first ordered distance equation holds at the common literal conic point. -/
theorem coordinateP_sq (c : K) :
    coordinateP c ^ 2 = (coordinateU c + 1) ^ 2 + (coordinateV c - 2) ^ 2 := by
  rw [coordinateP, Biquadratic.CoordinateAlgebra.coordinate₁_sq]
  change (algebraMap (AdjacentConicLiteralModel.CoordinateRing c) (CoordinateRing c))
    ((AdjacentConicLiteralModel.coordinateU c + 1) ^ 2 +
      (AdjacentConicLiteralModel.coordinateV c - 2) ^ 2) = _
  simp only [map_add, map_sub, map_pow, map_one, map_ofNat, coordinateU, coordinateV]

omit [CharZero K] in
/-- The second ordered distance equation holds at the same literal conic point. -/
theorem coordinateQ_sq (c : K) :
    coordinateQ c ^ 2 = (coordinateU c - 1) ^ 2 + (coordinateV c - 2) ^ 2 := by
  rw [coordinateQ, Biquadratic.CoordinateAlgebra.coordinate₂_sq]
  change (algebraMap (AdjacentConicLiteralModel.CoordinateRing c) (CoordinateRing c))
    ((AdjacentConicLiteralModel.coordinateU c - 1) ^ 2 +
      (AdjacentConicLiteralModel.coordinateV c - 2) ^ 2) = _
  simp only [map_add, map_sub, map_pow, map_one, map_ofNat, coordinateU, coordinateV]

/-- The target is constructed using the actual parametrization algebra. -/
abbrev functionField (c : K) (hc : c ≠ 0) :
    IntermediateField (RatFunc K) (AlgebraicClosure (RatFunc K)) := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  exact Biquadratic.CoordinateAlgebra.field (AdjacentConicLiteralModel.CoordinateRing c)
    (RatFunc K) (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)

/-- Equality of the actual intermediate fields, obtained by mapping the two literal radicands. -/
theorem functionField_eq (c : K) (hc : c ≠ 0) :
    functionField c hc = AdjacentGenus.field c := by
  change Biquadratic.field (RatFunc K)
    (AdjacentConicLiteralModel.parametrization c hc (AdjacentConicRadicands.radicand c 0))
    (AdjacentConicLiteralModel.parametrization c hc (AdjacentConicRadicands.radicand c 1)) = _
  rw [AdjacentConicRadicands.parametrization_radicand,
    AdjacentConicRadicands.parametrization_radicand]

/-- The map from the full literal quotient to its constructed function field. -/
def embedding (c : K) (hc : c ≠ 0) : CoordinateRing c →+* functionField c hc := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  exact Biquadratic.CoordinateAlgebra.map (AdjacentConicLiteralModel.CoordinateRing c)
    (RatFunc K) (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)

@[simp] theorem embedding_base (c : K) (hc : c ≠ 0)
    (x : AdjacentConicLiteralModel.CoordinateRing c) :
    embedding c hc (algebraMap (AdjacentConicLiteralModel.CoordinateRing c) (CoordinateRing c) x) =
      algebraMap (RatFunc K) (functionField c hc) (AdjacentConicLiteralModel.parametrization c hc x) := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  exact Biquadratic.CoordinateAlgebra.map_algebraMap
    (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) _ _ x

/-- The literal embedding respects the original constant field. -/
def embeddingAlgHom (c : K) (hc : c ≠ 0) : CoordinateRing c →ₐ[K] functionField c hc where
  __ := embedding c hc
  commutes' x := by
    change embedding c hc (algebraMap K (CoordinateRing c) x) = _
    rw [IsScalarTower.algebraMap_apply K (AdjacentConicLiteralModel.CoordinateRing c)
      (CoordinateRing c), embedding_base, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply K (RatFunc K) (functionField c hc)]

/-- Coherence of constants through the actual source embedding. -/
theorem embeddingScalarTower (c : K) (hc : c ≠ 0) :
    letI : Algebra (CoordinateRing c) (functionField c hc) := (embedding c hc).toAlgebra
    IsScalarTower K (CoordinateRing c) (functionField c hc) :=
  IsScalarTower.of_algHom (embeddingAlgHom c hc)

@[simp] theorem embedding_U (c : K) (hc : c ≠ 0) :
    embedding c hc (coordinateU c) =
      algebraMap (RatFunc K) (functionField c hc) (AdjacentConic.u c) := by
  rw [coordinateU, embedding_base, AdjacentConicLiteralModel.parametrization_U]

@[simp] theorem embedding_V (c : K) (hc : c ≠ 0) :
    embedding c hc (coordinateV c) =
      algebraMap (RatFunc K) (functionField c hc) (AdjacentConic.v c) := by
  rw [coordinateV, embedding_base, AdjacentConicLiteralModel.parametrization_V]

/-- The first distance coordinate maps to the originally chosen first radical. -/
theorem embedding_P_coe (c : K) (hc : c ≠ 0) :
    (embedding c hc (coordinateP c) : AlgebraicClosure (RatFunc K)) =
      Multiquadratic.radical (RatFunc K) (AdjacentPlaceOrders.actualValue c 0) := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  change ((Biquadratic.CoordinateAlgebra.map _ _ _ _
    (Biquadratic.CoordinateAlgebra.coordinate₁ _ _ _) : functionField c hc) :
    AlgebraicClosure (RatFunc K)) = _
  rw [Biquadratic.CoordinateAlgebra.map_coordinate₁]
  change Multiquadratic.radical (RatFunc K)
    (AdjacentConicLiteralModel.parametrization c hc (AdjacentConicRadicands.radicand c 0)) = _
  rw [AdjacentConicRadicands.parametrization_radicand]

/-- The second distance coordinate maps to the originally chosen second radical. -/
theorem embedding_Q_coe (c : K) (hc : c ≠ 0) :
    (embedding c hc (coordinateQ c) : AlgebraicClosure (RatFunc K)) =
      Multiquadratic.radical (RatFunc K) (AdjacentPlaceOrders.actualValue c 1) := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  change ((Biquadratic.CoordinateAlgebra.map _ _ _ _
    (Biquadratic.CoordinateAlgebra.coordinate₂ _ _ _) : functionField c hc) :
    AlgebraicClosure (RatFunc K)) = _
  rw [Biquadratic.CoordinateAlgebra.map_coordinate₂]
  change Multiquadratic.radical (RatFunc K)
    (AdjacentConicLiteralModel.parametrization c hc (AdjacentConicRadicands.radicand c 1)) = _
  rw [AdjacentConicRadicands.parametrization_radicand]

/-- The polynomial independence theorem supplies the exact literal base hypotheses. -/
theorem mappedRadicands_independent (c : K) (hc : c ≠ 0) (h : AdjacentPolynomials.Admissible c) :
    let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
      (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
    Biquadratic.IndependentSquareclasses (RatFunc K)
      (algebraMap (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K)
        (AdjacentConicRadicands.radicand c 0))
      (algebraMap (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K)
        (AdjacentConicRadicands.radicand c 1)) := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  change Biquadratic.IndependentSquareclasses (RatFunc K)
    (AdjacentConicLiteralModel.parametrization c hc (AdjacentConicRadicands.radicand c 0))
    (AdjacentConicLiteralModel.parametrization c hc (AdjacentConicRadicands.radicand c 1))
  rw [AdjacentConicRadicands.parametrization_radicand,
    AdjacentConicRadicands.parametrization_radicand]
  exact AdjacentPlaceOrders.actualValue_independentSquareclasses h

/-- The full literal source embeds without losing a component or a relation. -/
theorem embedding_injective (c : K) (hc : c ≠ 0) (h : AdjacentPolynomials.Admissible c) :
    Function.Injective (embedding c hc) := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  exact Biquadratic.CoordinateAlgebra.map_injective
    (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) _ _
    (AdjacentConicLiteralModel.parametrization_injective c hc h.conic_ne_zero)
    (by norm_num) (mappedRadicands_independent c hc h)

theorem coordinateRing_isDomain (c : K) (h : AdjacentPolynomials.Admissible c) :
    IsDomain (CoordinateRing c) :=
  Function.Injective.isDomain (embedding c h.c_ne_zero) (embedding_injective c h.c_ne_zero h)

/-- The actual radical field is a fraction field of the full literal source quotient. -/
theorem isFractionRing (c : K) (hc : c ≠ 0) (h : AdjacentPolynomials.Admissible c) :
    let : Algebra (CoordinateRing c) (functionField c hc) := (embedding c hc).toAlgebra
    IsFractionRing (CoordinateRing c) (functionField c hc) := by
  let : Algebra (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    (AdjacentConicLiteralModel.parametrization c hc).toRingHom.toAlgebra
  let : IsFractionRing (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) :=
    AdjacentConicLiteralModel.isFractionRing c hc h.conic_ne_zero
  exact Biquadratic.CoordinateAlgebra.isFractionRing_coordinateRing
    (AdjacentConicLiteralModel.CoordinateRing c) (RatFunc K) _ _
    (by norm_num) (mappedRadicands_independent c hc h)

/-- The canonical fraction field of the literal quotient is identified as a
`K`-field through the proved embedding, rather than by an assumed isomorphism. -/
def fractionFieldEquiv (c : K) (hc : c ≠ 0) (h : AdjacentPolynomials.Admissible c) :
    FractionRing (CoordinateRing c) ≃ₐ[K] functionField c hc := by
  letI : IsDomain (CoordinateRing c) := coordinateRing_isDomain c h
  letI : Algebra (CoordinateRing c) (functionField c hc) := (embedding c hc).toAlgebra
  letI : IsScalarTower K (CoordinateRing c) (functionField c hc) := embeddingScalarTower c hc
  letI : IsFractionRing (CoordinateRing c) (functionField c hc) := isFractionRing c hc h
  exact (FractionRing.algEquiv (CoordinateRing c) (functionField c hc)).restrictScalars K

@[simp] theorem fractionFieldEquiv_algebraMap (c : K) (hc : c ≠ 0)
    (h : AdjacentPolynomials.Admissible c) (x : CoordinateRing c) :
    fractionFieldEquiv c hc h (algebraMap (CoordinateRing c) (FractionRing (CoordinateRing c)) x) =
      embedding c hc x := by
  let : IsDomain (CoordinateRing c) := coordinateRing_isDomain c h
  let : Algebra (CoordinateRing c) (functionField c hc) := (embedding c hc).toAlgebra
  let : IsScalarTower K (CoordinateRing c) (functionField c hc) := embeddingScalarTower c hc
  let : IsFractionRing (CoordinateRing c) (functionField c hc) := isFractionRing c hc h
  exact (FractionRing.algEquiv (CoordinateRing c) (functionField c hc)).commutes x

/-- The identified fraction field has the already derived degree four. -/
theorem degree_four (c : K) (hc : c ≠ 0) (h : AdjacentPolynomials.Admissible c) :
    Module.finrank (RatFunc K) (functionField c hc) = 4 := by
  rw [functionField_eq]
  exact AdjacentGenus.degree_four h

/-- Genus five for the actual fraction field of the literal adjacent source. -/
theorem genusFF_eq_five [IsAlgClosed K] (c : K) (hc : c ≠ 0)
    (h : AdjacentPolynomials.Admissible c) : genusFF K (functionField c hc) = 5 := by
  rw [functionField_eq]
  exact AdjacentGenus.genusFF_eq_five h

abbrev rationalFunctionField (c : ℚ) (hc : 0 < c) (hne : c ≠ 1) :=
  functionField (algebraMap ℚ K c) (AdjacentPolynomials.rational_admissible c hc hne).c_ne_zero

theorem rational_coordinateRing_isDomain (c : ℚ) (hc : 0 < c) (hne : c ≠ 1) :
    IsDomain (CoordinateRing (algebraMap ℚ K c)) :=
  coordinateRing_isDomain _ (AdjacentPolynomials.rational_admissible c hc hne)

theorem rational_genusFF_eq_five [IsAlgClosed K] (c : ℚ) (hc : 0 < c) (hne : c ≠ 1) :
    genusFF K (rationalFunctionField (K := K) c hc hne) = 5 :=
  genusFF_eq_five _ _ (AdjacentPolynomials.rational_admissible c hc hne)

end FourCorner.AdjacentCoordinateAlgebra

#print axioms FourCorner.AdjacentCoordinateAlgebra.functionField_eq
#print axioms FourCorner.AdjacentCoordinateAlgebra.embedding_injective
#print axioms FourCorner.AdjacentCoordinateAlgebra.coordinateRing_isDomain
#print axioms FourCorner.AdjacentCoordinateAlgebra.isFractionRing
#print axioms FourCorner.AdjacentCoordinateAlgebra.coordinateP_sq
#print axioms FourCorner.AdjacentCoordinateAlgebra.coordinateQ_sq
#print axioms FourCorner.AdjacentCoordinateAlgebra.embedding_P_coe
#print axioms FourCorner.AdjacentCoordinateAlgebra.embedding_Q_coe
#print axioms FourCorner.AdjacentCoordinateAlgebra.genusFF_eq_five
#print axioms FourCorner.AdjacentCoordinateAlgebra.rational_genusFF_eq_five

#print axioms FourCorner.AdjacentCoordinateAlgebra.embeddingAlgHom
#print axioms FourCorner.AdjacentCoordinateAlgebra.fractionFieldEquiv
#print axioms FourCorner.AdjacentCoordinateAlgebra.fractionFieldEquiv_algebraMap
