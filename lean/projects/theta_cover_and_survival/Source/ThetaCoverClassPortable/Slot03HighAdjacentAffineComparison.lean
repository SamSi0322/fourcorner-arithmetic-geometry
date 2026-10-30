import ThetaCoverClassPortable.Slot03HighAdjacentProjective

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Slot03HighAdjacentProjective
open Polynomial
universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev conicR (c : K) := AdjacentConicLiteralModel.CoordinateRing c
abbrev literalR (c : K) := AdjacentCoordinateAlgebra.CoordinateRing c
abbrev aX (c : K) (i : Fin 4) : affineRing c := Ideal.Quotient.mk (affineIdeal c) (MvPolynomial.X i)
abbrev aC (c : K) : K →+* affineRing c := (Ideal.Quotient.mk (affineIdeal c)).comp MvPolynomial.C

theorem affineEquation_zero (c : K) (i : Fin 3) :
    Ideal.Quotient.mk (affineIdeal c) (affineEquation c i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem affine_relation0 (c : K) :
    aC c (c^2-1) * aX c 0 ^ 2 + aC c (c^2) * aX c 1 ^ 2 - aC c (c^2*(c^2-1)) = 0 := by
  simpa only [affineEquation, aC, aX, RingHom.comp_apply, map_add, map_sub, map_mul, map_pow] using affineEquation_zero c 0

theorem affine_relation1 (c : K) : aX c 2 ^ 2 = (aX c 0 + 1)^2 + (aX c 1 - 2)^2 := by
  have h := affineEquation_zero c 1
  simp only [affineEquation, map_sub, map_pow, map_add, map_one, map_ofNat] at h
  linear_combination h

theorem affine_relation2 (c : K) : aX c 3 ^ 2 = (aX c 0 - 1)^2 + (aX c 1 - 2)^2 := by
  have h := affineEquation_zero c 2
  simp only [affineEquation, map_sub, map_pow, map_add, map_one, map_ofNat] at h
  linear_combination h

abbrev polynomialToAffine (c : K) : K[X] →+* affineRing c := Polynomial.eval₂RingHom (aC c) (aX c 0)

def conicToAffine (c : K) : conicR c →+* affineRing c :=
  AdjoinRoot.lift (polynomialToAffine c) (aX c 1) (by
    simp only [AdjacentConicPresentation.literalEquation, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X, polynomialToAffine,
      Polynomial.coe_eval₂RingHom]
    exact affine_relation0 c)

@[simp] theorem conicToAffine_U (c : K) :
    conicToAffine c (AdjacentConicLiteralModel.coordinateU c) = aX c 0 := by
  simp [conicToAffine, AdjacentConicLiteralModel.coordinateU,
    AdjacentConicPresentation.coordinateU, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
    polynomialToAffine]

@[simp] theorem conicToAffine_V (c : K) :
    conicToAffine c (AdjacentConicLiteralModel.coordinateV c) = aX c 1 := AdjoinRoot.lift_root _

@[simp] theorem conicToAffine_constants (c a : K) :
    conicToAffine c (algebraMap K (conicR c) a) = aC c a := by
  change conicToAffine c (AdjoinRoot.of _ (Polynomial.C a)) = _
  simp [conicToAffine, AdjoinRoot.lift_of, polynomialToAffine]

@[simp] theorem conicToAffine_rad0 (c : K) :
    conicToAffine c (AdjacentConicRadicands.radicand c 0) = (aX c 0 + 1)^2 + (aX c 1 - 2)^2 := by
  simp [AdjacentConicRadicands.radicand, map_ofNat]
@[simp] theorem conicToAffine_rad1 (c : K) :
    conicToAffine c (AdjacentConicRadicands.radicand c 1) = (aX c 0 - 1)^2 + (aX c 1 - 2)^2 := by
  simp [AdjacentConicRadicands.radicand, map_ofNat]

def literalToAffine (c : K) : literalR c →+* affineRing c :=
  Biquadratic.CoordinateAlgebra.lift (conicR c) (affineRing c) (conicToAffine c)
    (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)
    (aX c 2) (aX c 3)
    (by rw [conicToAffine_rad0]; exact affine_relation1 c)
    (by rw [conicToAffine_rad1]; exact affine_relation2 c)

@[simp] theorem literalToAffine_U (c : K) :
    literalToAffine c (AdjacentCoordinateAlgebra.coordinateU c) = aX c 0 := by
  simp [literalToAffine, AdjacentCoordinateAlgebra.coordinateU]
@[simp] theorem literalToAffine_V (c : K) :
    literalToAffine c (AdjacentCoordinateAlgebra.coordinateV c) = aX c 1 := by
  simp [literalToAffine, AdjacentCoordinateAlgebra.coordinateV]
@[simp] theorem literalToAffine_P (c : K) :
    literalToAffine c (AdjacentCoordinateAlgebra.coordinateP c) = aX c 2 := by
  simp [literalToAffine, AdjacentCoordinateAlgebra.coordinateP]
@[simp] theorem literalToAffine_Q (c : K) :
    literalToAffine c (AdjacentCoordinateAlgebra.coordinateQ c) = aX c 3 := by
  simp [literalToAffine, AdjacentCoordinateAlgebra.coordinateQ]
@[simp] theorem literalToAffine_constants (c a : K) :
    literalToAffine c (algebraMap K (literalR c) a) = aC c a := by
  rw [IsScalarTower.algebraMap_apply K (conicR c) (literalR c)]
  simp [literalToAffine]

theorem conic_relation (c : K) :
    algebraMap K (conicR c) (c^2-1) * AdjacentConicLiteralModel.coordinateU c ^ 2 +
    algebraMap K (conicR c) (c^2) * AdjacentConicLiteralModel.coordinateV c ^ 2 -
    algebraMap K (conicR c) (c^2*(c^2-1)) = 0 := by
  have h := AdjoinRoot.eval₂_root (AdjacentConicPresentation.literalEquation c (c^2-1))
  change (C (C (c^2-1) * X^2) + C (C (c^2)) * X^2 - C (C (c^2*(c^2-1))) : K[X][X]).eval₂
    (AdjoinRoot.of (AdjacentConicPresentation.literalEquation c (c^2-1)))
    (AdjoinRoot.root (AdjacentConicPresentation.literalEquation c (c^2-1))) = 0 at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, map_mul, map_pow] at h
  simpa only [AdjacentConicLiteralModel.coordinateU, AdjacentConicLiteralModel.coordinateV,
    AdjacentConicPresentation.coordinateU, AdjacentConicPresentation.coordinateV,
    AdjoinRoot.algebraMap_eq', AdjoinRoot.algebraMap_eq, Polynomial.algebraMap_apply,
    RingHom.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    map_mul, map_pow, map_sub, map_one] using h

def affineEval (c : K) : AffineAmbient K →+* literalR c :=
  MvPolynomial.eval₂Hom (algebraMap K (literalR c))
    ![AdjacentCoordinateAlgebra.coordinateU c, AdjacentCoordinateAlgebra.coordinateV c,
      AdjacentCoordinateAlgebra.coordinateP c, AdjacentCoordinateAlgebra.coordinateQ c]

theorem affineEval_equation (c : K) (i : Fin 3) : affineEval c (affineEquation c i) = 0 := by
  fin_cases i
  · have h := congrArg (algebraMap (conicR c) (literalR c)) (conic_relation c)
    simpa [affineEval, affineEquation, map_mul, map_pow, map_add, map_sub,
      AdjacentCoordinateAlgebra.coordinateU, AdjacentCoordinateAlgebra.coordinateV,
      ← IsScalarTower.algebraMap_apply K (conicR c) (literalR c)] using h
  · simp [affineEval, affineEquation, AdjacentCoordinateAlgebra.coordinateP_sq]
  · simp [affineEval, affineEquation, AdjacentCoordinateAlgebra.coordinateQ_sq]

def affineToLiteral (c : K) : affineRing c →+* literalR c :=
  Ideal.Quotient.lift (affineIdeal c) (affineEval c) (by
    have h : affineIdeal c ≤ RingHom.ker (affineEval c) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact affineEval_equation c i
    exact fun p hp => h hp)

@[simp] theorem affineToLiteral_aX (c : K) (i : Fin 4) :
    affineToLiteral c (aX c i) =
      ![AdjacentCoordinateAlgebra.coordinateU c, AdjacentCoordinateAlgebra.coordinateV c,
      AdjacentCoordinateAlgebra.coordinateP c, AdjacentCoordinateAlgebra.coordinateQ c] i := by
  simp [affineToLiteral, affineEval, aX, Ideal.Quotient.lift_mk]
@[simp] theorem affineToLiteral_aC (c a : K) :
    affineToLiteral c (aC c a) = algebraMap K (literalR c) a := by
  simp [affineToLiteral, affineEval, aC, Ideal.Quotient.lift_mk]

theorem conicToAffine_inverse (c : K) :
    (affineToLiteral c).comp (conicToAffine c) = algebraMap (conicR c) (literalR c) := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      change affineToLiteral c (conicToAffine c (algebraMap K (conicR c) a)) =
        algebraMap K (literalR c) a
      rw [conicToAffine_constants, affineToLiteral_aC]
    · change affineToLiteral c (conicToAffine c (AdjacentConicLiteralModel.coordinateU c)) =
        AdjacentCoordinateAlgebra.coordinateU c
      rw [conicToAffine_U, affineToLiteral_aX]
      rfl
  · change affineToLiteral c (conicToAffine c (AdjacentConicLiteralModel.coordinateV c)) =
      AdjacentCoordinateAlgebra.coordinateV c
    rw [conicToAffine_V, affineToLiteral_aX]
    rfl

theorem affineToLiteral_inverse (c : K) :
    (literalToAffine c).comp (affineToLiteral c) = RingHom.id (affineRing c) := by
  have h : (literalToAffine c).comp (affineEval c) = Ideal.Quotient.mk (affineIdeal c) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, affineEval, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      exact literalToAffine_constants c a
    · intro i
      fin_cases i <;> simp [affineEval, literalToAffine_U, literalToAffine_V,
        literalToAffine_P, literalToAffine_Q]
  apply RingHom.ext
  intro a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  exact RingHom.congr_fun h p

theorem literalToAffine_inverse (c : K) :
    (affineToLiteral c).comp (literalToAffine c) = RingHom.id (literalR c) := by
  apply Biquadratic.CoordinateAlgebra.ringHom_ext (conicR c) (literalR c)
    (AdjacentConicRadicands.radicand c 0) (AdjacentConicRadicands.radicand c 1)
  · intro a
    change affineToLiteral c (literalToAffine c (algebraMap (conicR c) (literalR c) a)) = _
    rw [show literalToAffine c (algebraMap (conicR c) (literalR c) a) = conicToAffine c a by
      simp only [literalToAffine, Biquadratic.CoordinateAlgebra.lift_algebraMap]]
    exact RingHom.congr_fun (conicToAffine_inverse c) a
  · change affineToLiteral c (literalToAffine c (AdjacentCoordinateAlgebra.coordinateP c)) =
      AdjacentCoordinateAlgebra.coordinateP c
    rw [literalToAffine_P, affineToLiteral_aX]
    rfl
  · change affineToLiteral c (literalToAffine c (AdjacentCoordinateAlgebra.coordinateQ c)) =
      AdjacentCoordinateAlgebra.coordinateQ c
    rw [literalToAffine_Q, affineToLiteral_aX]
    rfl

/-- Full equation quotient equivalence, preserving all four ordered affine coordinates. -/
def affineLiteralEquiv (c : K) : affineRing c ≃+* literalR c :=
  RingEquiv.ofRingHom (affineToLiteral c) (literalToAffine c)
    (literalToAffine_inverse c) (affineToLiteral_inverse c)

def literalChartSchemeIso (c : K) :
    (AlgebraicGeometry.Proj.basicOpen (quotientGrading c)
      (Ideal.Quotient.mk (ideal c) (MvPolynomial.X (4 : Fin 5)))).toScheme ≅
      AlgebraicGeometry.Spec (.of (literalR c)) :=
  chartSchemeIso c ≪≫ AlgebraicGeometry.Scheme.Spec.mapIso ((affineLiteralEquiv c).symm.toCommRingCatIso.op)

#print axioms affineLiteralEquiv
#print axioms literalChartSchemeIso
#print axioms literalToAffine
#print axioms affineToLiteral
end FourCorner.Slot03HighAdjacentProjective
