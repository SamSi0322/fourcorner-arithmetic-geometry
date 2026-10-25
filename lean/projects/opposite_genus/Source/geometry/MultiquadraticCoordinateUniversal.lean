import geometry.MultiquadraticCoordinateAlgebra

/-!
# Universal property of the literal three-quadratic coordinate algebra

Over arbitrary commutative rings, a coefficient map and three elements satisfying
the three defining square equations give a unique ring homomorphism out of the
coordinate algebra. No field, domain, or squareclass hypothesis is used.
-/

noncomputable section

namespace FourCorner.Multiquadratic.CoordinateUniversal

open Polynomial CoordinateAlgebra

variable (R S : Type*) [CommRing R] [CommRing S]

/-- Lift the coefficient map across the first literal quadratic equation. -/
def lift₁ (i : R →+* S) (a : R) (p : S) (hp : p ^ 2 = i a) : Stage₁ R a →+* S :=
  AdjoinRoot.lift i p (by
    simp only [equation₁, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hp, sub_self])

@[simp] theorem lift₁_root (i : R →+* S) (a : R) (p : S) (hp : p ^ 2 = i a) :
    lift₁ R S i a p hp (AdjoinRoot.root (equation₁ R a)) = p :=
  AdjoinRoot.lift_root _

@[simp] theorem lift₁_algebraMap (i : R →+* S) (a : R) (p : S)
    (hp : p ^ 2 = i a) (x : R) :
    lift₁ R S i a p hp (algebraMap R (Stage₁ R a) x) = i x :=
  AdjoinRoot.lift_of _

/-- Lift through the second equation using the already constructed first map. -/
def lift₂ (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) : Stage₂ R a b →+* S :=
  AdjoinRoot.lift (lift₁ R S i a p hp) q (by
    simp only [equation₂, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
      lift₁_algebraMap, hq, sub_self])

@[simp] theorem lift₂_root (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) :
    lift₂ R S i a b p q hp hq (AdjoinRoot.root (equation₂ R a b)) = q :=
  AdjoinRoot.lift_root _

@[simp] theorem lift₂_of (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (x : Stage₁ R a) :
    lift₂ R S i a b p q hp hq (algebraMap (Stage₁ R a) (Stage₂ R a b) x) =
      lift₁ R S i a p hp x := AdjoinRoot.lift_of _

@[simp] theorem lift₂_algebraMap (i : R →+* S) (a b : R) (p q : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (x : R) :
    lift₂ R S i a b p q hp hq (algebraMap R (Stage₂ R a b) x) = i x := by
  rw [IsScalarTower.algebraMap_apply R (Stage₁ R a) (Stage₂ R a b), lift₂_of,
    lift₁_algebraMap]

/-- The map from the full coordinate algebra determined by three square roots. -/
def lift (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    Stage₃ R a b c →+* S :=
  AdjoinRoot.lift (lift₂ R S i a b p q hp hq) r (by
    simp only [equation₃, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
      lift₂_algebraMap, hr, sub_self])

@[simp] theorem lift_root (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    lift R S i a b c p q r hp hq hr (AdjoinRoot.root (equation₃ R a b c)) = r :=
  AdjoinRoot.lift_root _

@[simp] theorem lift_of (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) (x : Stage₂ R a b) :
    lift R S i a b c p q r hp hq hr (algebraMap (Stage₂ R a b) (Stage₃ R a b c) x) =
      lift₂ R S i a b p q hp hq x := AdjoinRoot.lift_of _

@[simp] theorem lift_algebraMap (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) (x : R) :
    lift R S i a b c p q r hp hq hr (algebraMap R (Stage₃ R a b c) x) = i x := by
  rw [IsScalarTower.algebraMap_apply R (Stage₂ R a b) (Stage₃ R a b c), lift_of,
    lift₂_algebraMap]

@[simp] theorem lift_coordinate₁ (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    lift R S i a b c p q r hp hq hr (coordinate₁ R a b c) = p := by
  rw [coordinate₁, IsScalarTower.algebraMap_apply (Stage₁ R a) (Stage₂ R a b),
    lift_of, lift₂_of, lift₁_root]

@[simp] theorem lift_coordinate₂ (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    lift R S i a b c p q r hp hq hr (coordinate₂ R a b c) = q := by
  rw [coordinate₂, lift_of, lift₂_root]

@[simp] theorem lift_coordinate₃ (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    lift R S i a b c p q r hp hq hr (coordinate₃ R a b c) = r :=
  lift_root R S i a b c p q r hp hq hr

/-- Maps out of the three-stage coordinate ring are determined by coefficients
and the three coordinate images. -/
theorem ringHom_ext (a b c : R) (f g : Stage₃ R a b c →+* S)
    (hR : ∀ x : R, f (algebraMap R (Stage₃ R a b c) x) =
      g (algebraMap R (Stage₃ R a b c) x))
    (h₁ : f (coordinate₁ R a b c) = g (coordinate₁ R a b c))
    (h₂ : f (coordinate₂ R a b c) = g (coordinate₂ R a b c))
    (h₃ : f (coordinate₃ R a b c) = g (coordinate₃ R a b c)) : f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply AdjoinRoot.ringHom_ext
    · apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro x
        exact hR x
      · exact h₁
    · exact h₂
  · exact h₃

/-- The constructed map is the unique one with the prescribed coefficient and coordinate images. -/
theorem lift_unique (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c)
    (f : Stage₃ R a b c →+* S)
    (hR : ∀ x : R, f (algebraMap R (Stage₃ R a b c) x) = i x)
    (h₁ : f (coordinate₁ R a b c) = p) (h₂ : f (coordinate₂ R a b c) = q)
    (h₃ : f (coordinate₃ R a b c) = r) : f = lift R S i a b c p q r hp hq hr := by
  apply ringHom_ext R S a b c
  · intro x
    rw [lift_algebraMap]
    exact hR x
  · rw [lift_coordinate₁]
    exact h₁
  · rw [lift_coordinate₂]
    exact h₂
  · rw [lift_coordinate₃]
    exact h₃

/-- The complete universal property over arbitrary commutative rings. -/
theorem existsUnique_lift (i : R →+* S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    ∃! f : Stage₃ R a b c →+* S,
      (∀ x : R, f (algebraMap R (Stage₃ R a b c) x) = i x) ∧
      f (coordinate₁ R a b c) = p ∧ f (coordinate₂ R a b c) = q ∧
      f (coordinate₃ R a b c) = r := by
  refine ⟨lift R S i a b c p q r hp hq hr, ?_, ?_⟩
  · exact ⟨lift_algebraMap R S i a b c p q r hp hq hr,
      lift_coordinate₁ R S i a b c p q r hp hq hr,
      lift_coordinate₂ R S i a b c p q r hp hq hr,
      lift_coordinate₃ R S i a b c p q r hp hq hr⟩
  · intro f hf
    exact lift_unique R S i a b c p q r hp hq hr f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2

section Algebra

variable {K : Type*} [CommSemiring K] [Algebra K R] [Algebra K S]

/-- The same universal map respects a smaller scalar ring whenever the coefficient map does. -/
def liftAlgHom (i : R →ₐ[K] S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    Stage₃ R a b c →ₐ[K] S where
  __ := lift R S i.toRingHom a b c p q r hp hq hr
  commutes' x := by
    change lift R S i.toRingHom a b c p q r hp hq hr (algebraMap K (Stage₃ R a b c) x) = _
    rw [IsScalarTower.algebraMap_apply K R (Stage₃ R a b c), lift_algebraMap]
    exact i.commutes x

@[simp] theorem liftAlgHom_toRingHom (i : R →ₐ[K] S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c) :
    (liftAlgHom R S i a b c p q r hp hq hr).toRingHom =
      lift R S i.toRingHom a b c p q r hp hq hr := rfl

@[simp] theorem liftAlgHom_apply (i : R →ₐ[K] S) (a b c : R) (p q r : S)
    (hp : p ^ 2 = i a) (hq : q ^ 2 = i b) (hr : r ^ 2 = i c)
    (x : Stage₃ R a b c) :
    liftAlgHom R S i a b c p q r hp hq hr x =
      lift R S i.toRingHom a b c p q r hp hq hr x := rfl

end Algebra

end FourCorner.Multiquadratic.CoordinateUniversal

#print axioms FourCorner.Multiquadratic.CoordinateUniversal.lift_algebraMap
#print axioms FourCorner.Multiquadratic.CoordinateUniversal.lift_coordinate₁
#print axioms FourCorner.Multiquadratic.CoordinateUniversal.lift_coordinate₂
#print axioms FourCorner.Multiquadratic.CoordinateUniversal.lift_coordinate₃

#print axioms FourCorner.Multiquadratic.CoordinateUniversal.ringHom_ext
#print axioms FourCorner.Multiquadratic.CoordinateUniversal.lift_unique
#print axioms FourCorner.Multiquadratic.CoordinateUniversal.existsUnique_lift
#print axioms FourCorner.Multiquadratic.CoordinateUniversal.liftAlgHom
