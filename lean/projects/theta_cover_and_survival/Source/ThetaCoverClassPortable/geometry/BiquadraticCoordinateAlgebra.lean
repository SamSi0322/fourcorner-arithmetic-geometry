import ThetaCoverClassPortable.geometry.MultiquadraticCoordinateAlgebra
import ThetaCoverClassPortable.geometry.MultiquadraticCoordinateUniversal
import ThetaCoverClassPortable.geometry.BiquadraticField

/-!
# The literal two-quadratic coordinate ring and its fraction field

The coordinate ring is the existing second iterated `AdjoinRoot` quotient.
Its map lands in the existing second radical-field stage, with the ordered
coordinates sent to the corresponding roots. Injectivity, the domain property,
and the fraction-field identification are derived from squareclass independence.
-/

noncomputable section

namespace FourCorner.Biquadratic.CoordinateAlgebra

open Polynomial


variable (R : Type*) [CommRing R]

/-- The actual iterated quotient by the two literal quadratic equations. -/
abbrev CoordinateRing (a b : R) := Multiquadratic.CoordinateAlgebra.Stage₂ R a b

/-- The first coordinate, carried from the first quotient to the second. -/
def coordinate₁ (a b : R) : CoordinateRing R a b :=
  algebraMap (Multiquadratic.CoordinateAlgebra.Stage₁ R a) (CoordinateRing R a b) (AdjoinRoot.root (Multiquadratic.CoordinateAlgebra.equation₁ R a))

/-- The newly adjoined second coordinate. -/
def coordinate₂ (a b : R) : CoordinateRing R a b := AdjoinRoot.root (Multiquadratic.CoordinateAlgebra.equation₂ R a b)

@[simp] theorem coordinate₁_sq (a b : R) :
    coordinate₁ R a b ^ 2 = algebraMap R (CoordinateRing R a b) a := by
  have h := AdjoinRoot.eval₂_root (Multiquadratic.CoordinateAlgebra.equation₁ R a)
  change (X ^ 2 - C a : R[X]).eval₂ (AdjoinRoot.of (Multiquadratic.CoordinateAlgebra.equation₁ R a))
    (AdjoinRoot.root (Multiquadratic.CoordinateAlgebra.equation₁ R a)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  rw [coordinate₁, ← map_pow, h]
  rfl

@[simp] theorem coordinate₂_sq (a b : R) :
    coordinate₂ R a b ^ 2 = algebraMap R (CoordinateRing R a b) b := by
  have h := AdjoinRoot.eval₂_root (Multiquadratic.CoordinateAlgebra.equation₂ R a b)
  change (X ^ 2 - C (algebraMap R (Multiquadratic.CoordinateAlgebra.Stage₁ R a) b) : (Multiquadratic.CoordinateAlgebra.Stage₁ R a)[X]).eval₂
    (AdjoinRoot.of (Multiquadratic.CoordinateAlgebra.equation₂ R a b)) (AdjoinRoot.root (Multiquadratic.CoordinateAlgebra.equation₂ R a b)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

/-- The literal coordinate ring is finite free of rank four over its coefficient ring. -/
theorem finrank_coordinateRing [Nontrivial R] (a b : R) :
    Module.finrank R (CoordinateRing R a b) = 4 := Multiquadratic.CoordinateAlgebra.finrank₂ R a b

section Universal

open Multiquadratic.CoordinateAlgebra

variable (S : Type*) [CommRing S]

/-- Two-coordinate ring maps are determined by their coefficients and coordinate images. -/
theorem ringHom_ext (a b : R) (f g : Stage₂ R a b →+* S)
    (hR : ∀ x : R, f (algebraMap R (Stage₂ R a b) x) =
      g (algebraMap R (Stage₂ R a b) x))
    (h₁ : f (coordinate₁ R a b) = g (coordinate₁ R a b))
    (h₂ : f (coordinate₂ R a b) = g (coordinate₂ R a b)) : f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro x
      exact hR x
    · exact h₁
  · exact h₂

/-- The universal map supplied by the two literal quadratic equations. -/
abbrev lift (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) : Stage₂ R a b →+* S :=
  Multiquadratic.CoordinateUniversal.lift₂ R S i a b p q hp hq

@[simp] theorem lift_algebraMap (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (x : R) :
    lift R S i a b p q hp hq (algebraMap R (Stage₂ R a b) x) = i x :=
  Multiquadratic.CoordinateUniversal.lift₂_algebraMap R S i a b p q hp hq x

@[simp] theorem lift_coordinate₁ (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) :
    lift R S i a b p q hp hq (coordinate₁ R a b) = p := by
  exact (Multiquadratic.CoordinateUniversal.lift₂_of R S i a b p q hp hq
    (AdjoinRoot.root (equation₁ R a))).trans
      (Multiquadratic.CoordinateUniversal.lift₁_root R S i a p hp)

@[simp] theorem lift_coordinate₂ (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) :
    lift R S i a b p q hp hq (coordinate₂ R a b) = q :=
  Multiquadratic.CoordinateUniversal.lift₂_root R S i a b p q hp hq

/-- Every map with these coefficient and coordinate images is the universal map. -/
theorem lift_unique (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (f : Stage₂ R a b →+* S)
    (hR : ∀ x : R, f (algebraMap R (Stage₂ R a b) x) = i x)
    (h₁ : f (coordinate₁ R a b) = p) (h₂ : f (coordinate₂ R a b) = q) :
    f = lift R S i a b p q hp hq := by
  apply ringHom_ext R S a b
  · intro x
    rw [lift_algebraMap]
    exact hR x
  · rw [lift_coordinate₁]
    exact h₁
  · rw [lift_coordinate₂]
    exact h₂

/-- The complete two-coordinate universal property requires only commutative rings. -/
theorem existsUnique_lift (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) :
    ∃! f : Stage₂ R a b →+* S,
      (∀ x : R, f (algebraMap R (Stage₂ R a b) x) = i x) ∧
      f (coordinate₁ R a b) = p ∧ f (coordinate₂ R a b) = q := by
  refine ⟨lift R S i a b p q hp hq, ?_, ?_⟩
  · exact ⟨lift_algebraMap R S i a b p q hp hq,
      lift_coordinate₁ R S i a b p q hp hq, lift_coordinate₂ R S i a b p q hp hq⟩
  · intro f hf
    exact lift_unique R S i a b p q hp hq f hf.1 hf.2.1 hf.2.2

section Algebra
variable {K : Type*} [CommSemiring K] [Algebra K R] [Algebra K S]

/-- The universal map respects any smaller scalar ring respected by its coefficient map. -/
def liftAlgHom (i : R →ₐ[K] S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) : Stage₂ R a b →ₐ[K] S where
  __ := lift R S i.toRingHom a b p q hp hq
  commutes' x := by
    change lift R S i.toRingHom a b p q hp hq (algebraMap K (Stage₂ R a b) x) = _
    rw [IsScalarTower.algebraMap_apply K R (Stage₂ R a b), lift_algebraMap]
    exact i.commutes x

@[simp] theorem liftAlgHom_apply (i : R →ₐ[K] S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (x : Stage₂ R a b) :
    liftAlgHom R S i a b p q hp hq x = lift R S i.toRingHom a b p q hp hq x := rfl

end Algebra


end Universal

variable (F : Type*) [Field F] [Algebra R F]

/-- The unchanged actual field generated by the two mapped radicands. -/
abbrev field (a b : R) := Multiquadratic.CoordinateAlgebra.field₂ R F a b

/-- The explicit map from the two-coordinate quotient into the actual radical field. -/
abbrev map (a b : R) : CoordinateRing R a b →+* field R F a b := Multiquadratic.CoordinateAlgebra.map₂ R F a b

@[simp] theorem map_algebraMap (a b x : R) :
    map R F a b (algebraMap R (CoordinateRing R a b) x) =
      algebraMap F (field R F a b) (algebraMap R F x) := Multiquadratic.CoordinateAlgebra.map₂_algebraMap R F a b x

@[simp] theorem map_coordinate₁ (a b : R) :
    map R F a b (coordinate₁ R a b) =
      Biquadratic.root₁ F (algebraMap R F a) (algebraMap R F b) := by
  rw [coordinate₁, Multiquadratic.CoordinateAlgebra.map₂_of, Multiquadratic.CoordinateAlgebra.map₁_root]
  rfl

@[simp] theorem map_coordinate₂ (a b : R) :
    map R F a b (coordinate₂ R a b) =
      Biquadratic.root₂ F (algebraMap R F a) (algebraMap R F b) :=
  Multiquadratic.CoordinateAlgebra.map₂_root R F a b

/-- Squareclass independence proves that the explicit quotient map is injective. -/
theorem map_injective (a b : R) (hi : Function.Injective (algebraMap R F))
    (h2 : (2 : F) ≠ 0)
    (hind : Biquadratic.IndependentSquareclasses F (algebraMap R F a) (algebraMap R F b)) :
    Function.Injective (map R F a b) :=
  Multiquadratic.CoordinateAlgebra.map₂_injective R F a b hi h2 hind.first hind.second hind.product

/-- The literal two-coordinate quotient is a domain by its actual field embedding. -/
theorem coordinateRing_isDomain (a b : R) (hi : Function.Injective (algebraMap R F))
    (h2 : (2 : F) ≠ 0)
    (hind : Biquadratic.IndependentSquareclasses F (algebraMap R F a) (algebraMap R F b)) :
    IsDomain (CoordinateRing R a b) :=
  Function.Injective.isDomain (map R F a b) (map_injective R F a b hi h2 hind)

instance (priority := 900) targetAlgebra (a b : R) : Algebra R (field R F a b) :=
  ((algebraMap F (field R F a b)).comp (algebraMap R F)).toAlgebra

instance coordinateAlgebra (a b : R) : Algebra (CoordinateRing R a b) (field R F a b) :=
  (map R F a b).toAlgebra

instance targetScalarTower (a b : R) : IsScalarTower R F (field R F a b) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance coordinateScalarTower (a b : R) :
    IsScalarTower R (CoordinateRing R a b) (field R F a b) :=
  IsScalarTower.of_algebraMap_eq fun x => (map_algebraMap R F a b x).symm

/-- If the base field is the coefficient fraction field, the actual two-radical
field is the fraction field of the literal coordinate quotient. -/
theorem isFractionRing_coordinateRing [IsFractionRing R F] (a b : R)
    (h2 : (2 : F) ≠ 0)
    (hind : Biquadratic.IndependentSquareclasses F (algebraMap R F a) (algebraMap R F b)) :
    IsFractionRing (CoordinateRing R a b) (field R F a b) := by
  have : FaithfulSMul (CoordinateRing R a b) (field R F a b) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (map_injective R F a b (IsFractionRing.injective R F) h2 hind)
  let T : Set (field R F a b) :=
    {Biquadratic.root₁ F (algebraMap R F a) (algebraMap R F b),
      Biquadratic.root₂ F (algebraMap R F a) (algebraMap R F b)}
  apply Multiquadratic.GeneratedFractionField.of_adjoin_eq_top R F
    (CoordinateRing R a b) (field R F a b) T
  · exact Biquadratic.roots_generate_algebra F _ _
  · intro x hx
    rcases hx with h | h
    · exact ⟨coordinate₁ R a b, (map_coordinate₁ R F a b).trans h.symm⟩
    · exact ⟨coordinate₂ R a b, (map_coordinate₂ R F a b).trans h.symm⟩

end FourCorner.Biquadratic.CoordinateAlgebra

#print axioms FourCorner.Biquadratic.CoordinateAlgebra.coordinate₁_sq
#print axioms FourCorner.Biquadratic.CoordinateAlgebra.coordinate₂_sq
#print axioms FourCorner.Biquadratic.CoordinateAlgebra.finrank_coordinateRing
#print axioms FourCorner.Biquadratic.CoordinateAlgebra.map_injective
#print axioms FourCorner.Biquadratic.CoordinateAlgebra.coordinateRing_isDomain
#print axioms FourCorner.Biquadratic.CoordinateAlgebra.isFractionRing_coordinateRing

#print axioms FourCorner.Biquadratic.CoordinateAlgebra.ringHom_ext
#print axioms FourCorner.Biquadratic.CoordinateAlgebra.existsUnique_lift
#print axioms FourCorner.Biquadratic.CoordinateAlgebra.liftAlgHom
