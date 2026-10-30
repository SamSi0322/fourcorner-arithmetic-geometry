import ThetaCoverClassPortable.geometry.MultiquadraticCoordinateAlgebra
import ThetaCoverClassPortable.geometry.AdjoinRootBaseChange

/-!
# Scalar extension of the actual three-coordinate algebra

Each equivalence below extends the preceding coefficient equivalence across
one literal quadratic quotient. Thus the final equivalence transports all
three quotient coordinates, including their coefficient inclusions.
-/

noncomputable section

namespace FourCorner.Multiquadratic.BaseChange

open CoordinateAlgebra
open scoped TensorProduct

variable {A S R T : Type*}
  [CommRing A] [CommRing S] [CommRing R] [CommRing T]
  [Algebra A S] [Algebra A R] [Algebra S T]

variable (e : S ⊗[A] R ≃ₐ[S] T)

/-- Transport of the first literal quadratic quotient. -/
def stage₁Equiv (a : R) :
    S ⊗[A] Stage₁ R a ≃ₐ[S] Stage₁ T (e (1 ⊗ₜ[A] a)) :=
  AdjoinRootBaseChange.quadraticTowerTransport e a (e (1 ⊗ₜ[A] a)) rfl

@[simp] theorem stage₁Equiv_root (a : R) :
    stage₁Equiv e a (1 ⊗ₜ[A] AdjoinRoot.root (equation₁ R a)) =
      AdjoinRoot.root (equation₁ T (e (1 ⊗ₜ[A] a))) :=
  AdjoinRootBaseChange.quadraticTowerTransport_root e a (e (1 ⊗ₜ[A] a)) rfl

@[simp] theorem stage₁Equiv_algebraMap (a x : R) :
    stage₁Equiv e a (1 ⊗ₜ[A] algebraMap R (Stage₁ R a) x) =
      algebraMap T (Stage₁ T (e (1 ⊗ₜ[A] a))) (e (1 ⊗ₜ[A] x)) :=
  AdjoinRootBaseChange.quadraticTowerTransport_algebraMap e a x
    (e (1 ⊗ₜ[A] a)) rfl

/-- Transport of the second quotient over the transported first quotient. -/
def stage₂Equiv (a b : R) :
    S ⊗[A] Stage₂ R a b ≃ₐ[S]
      Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) :=
  AdjoinRootBaseChange.quadraticTowerTransport (stage₁Equiv e a)
    (algebraMap R (Stage₁ R a) b)
    (algebraMap T (Stage₁ T (e (1 ⊗ₜ[A] a))) (e (1 ⊗ₜ[A] b)))
    (stage₁Equiv_algebraMap e a b)

@[simp] theorem stage₂Equiv_root (a b : R) :
    stage₂Equiv e a b (1 ⊗ₜ[A] AdjoinRoot.root (equation₂ R a b)) =
      AdjoinRoot.root (equation₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b))) :=
  AdjoinRootBaseChange.quadraticTowerTransport_root _ _ _ _

@[simp] theorem stage₂Equiv_of (a b : R) (x : Stage₁ R a) :
    stage₂Equiv e a b
        (1 ⊗ₜ[A] algebraMap (Stage₁ R a) (Stage₂ R a b) x) =
      algebraMap (Stage₁ T (e (1 ⊗ₜ[A] a)))
        (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))
        (stage₁Equiv e a (1 ⊗ₜ[A] x)) :=
  AdjoinRootBaseChange.quadraticTowerTransport_algebraMap _ _ _ _ _

@[simp] theorem stage₂Equiv_algebraMap (a b x : R) :
    stage₂Equiv e a b (1 ⊗ₜ[A] algebraMap R (Stage₂ R a b) x) =
      algebraMap T (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))
        (e (1 ⊗ₜ[A] x)) := by
  rw [IsScalarTower.algebraMap_apply R (Stage₁ R a) (Stage₂ R a b),
    stage₂Equiv_of, stage₁Equiv_algebraMap,
    ← IsScalarTower.algebraMap_apply T (Stage₁ T (e (1 ⊗ₜ[A] a)))
      (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))]

/-- Scalar extension of all three actual quotient stages, for any given
equivalence of the scalar-extended coefficient ring. -/
def stage₃Equiv (a b c : R) :
    S ⊗[A] Stage₃ R a b c ≃ₐ[S]
      Stage₃ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c)) :=
  AdjoinRootBaseChange.quadraticTowerTransport (stage₂Equiv e a b)
    (algebraMap R (Stage₂ R a b) c)
    (algebraMap T (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))
      (e (1 ⊗ₜ[A] c)))
    (stage₂Equiv_algebraMap e a b c)

@[simp] theorem stage₃Equiv_root (a b c : R) :
    stage₃Equiv e a b c (1 ⊗ₜ[A] AdjoinRoot.root (equation₃ R a b c)) =
      AdjoinRoot.root (equation₃ T
        (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c))) :=
  AdjoinRootBaseChange.quadraticTowerTransport_root _ _ _ _

@[simp] theorem stage₃Equiv_of (a b c : R) (x : Stage₂ R a b) :
    stage₃Equiv e a b c
        (1 ⊗ₜ[A] algebraMap (Stage₂ R a b) (Stage₃ R a b c) x) =
      algebraMap (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))
        (Stage₃ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c)))
        (stage₂Equiv e a b (1 ⊗ₜ[A] x)) :=
  AdjoinRootBaseChange.quadraticTowerTransport_algebraMap _ _ _ _ _

@[simp] theorem stage₃Equiv_algebraMap (a b c x : R) :
    stage₃Equiv e a b c (1 ⊗ₜ[A] algebraMap R (Stage₃ R a b c) x) =
      algebraMap T
        (Stage₃ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c)))
        (e (1 ⊗ₜ[A] x)) := by
  rw [IsScalarTower.algebraMap_apply R (Stage₂ R a b) (Stage₃ R a b c),
    stage₃Equiv_of, stage₂Equiv_algebraMap,
    ← IsScalarTower.algebraMap_apply T
      (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))
      (Stage₃ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c)))]

/-- The final equivalence also transports the second coordinate through
its actual inclusion into the third quotient. -/
@[simp] theorem stage₃Equiv_root₂ (a b c : R) :
    stage₃Equiv e a b c
        (1 ⊗ₜ[A] algebraMap (Stage₂ R a b) (Stage₃ R a b c)
          (AdjoinRoot.root (equation₂ R a b))) =
      algebraMap (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))
        (Stage₃ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c)))
        (AdjoinRoot.root (equation₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))) := by
  rw [stage₃Equiv_of, stage₂Equiv_root]

/-- The first coordinate is preserved through both later coefficient maps. -/
@[simp] theorem stage₃Equiv_root₁ (a b c : R) :
    stage₃Equiv e a b c
        (1 ⊗ₜ[A] algebraMap (Stage₁ R a) (Stage₃ R a b c)
          (AdjoinRoot.root (equation₁ R a))) =
      algebraMap (Stage₁ T (e (1 ⊗ₜ[A] a)))
        (Stage₃ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c)))
        (AdjoinRoot.root (equation₁ T (e (1 ⊗ₜ[A] a)))) := by
  rw [IsScalarTower.algebraMap_apply (Stage₁ R a) (Stage₂ R a b) (Stage₃ R a b c),
    stage₃Equiv_of, stage₂Equiv_of, stage₁Equiv_root,
    ← IsScalarTower.algebraMap_apply (Stage₁ T (e (1 ⊗ₜ[A] a)))
      (Stage₂ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)))
      (Stage₃ T (e (1 ⊗ₜ[A] a)) (e (1 ⊗ₜ[A] b)) (e (1 ⊗ₜ[A] c)))]

/-- The canonical scalar-extension equivalence of the three-coordinate ring. -/
def tensorEquiv (a b c : R) :
    S ⊗[A] Stage₃ R a b c ≃ₐ[S]
      Stage₃ (S ⊗[A] R) (1 ⊗ₜ[A] a) (1 ⊗ₜ[A] b) (1 ⊗ₜ[A] c) :=
  stage₃Equiv (AlgEquiv.refl : S ⊗[A] R ≃ₐ[S] S ⊗[A] R) a b c

@[simp] theorem tensorEquiv_root (a b c : R) :
    tensorEquiv (S := S) a b c (1 ⊗ₜ[A] AdjoinRoot.root (equation₃ R a b c)) =
      AdjoinRoot.root (equation₃ (S ⊗[A] R)
        (1 ⊗ₜ[A] a) (1 ⊗ₜ[A] b) (1 ⊗ₜ[A] c)) :=
  stage₃Equiv_root (AlgEquiv.refl : S ⊗[A] R ≃ₐ[S] S ⊗[A] R) a b c

@[simp] theorem tensorEquiv_algebraMap (a b c x : R) :
    tensorEquiv (S := S) a b c
        (1 ⊗ₜ[A] algebraMap R (Stage₃ R a b c) x) =
      algebraMap (S ⊗[A] R)
        (Stage₃ (S ⊗[A] R) (1 ⊗ₜ[A] a) (1 ⊗ₜ[A] b) (1 ⊗ₜ[A] c))
        (1 ⊗ₜ[A] x) :=
  stage₃Equiv_algebraMap (AlgEquiv.refl : S ⊗[A] R ≃ₐ[S] S ⊗[A] R) a b c x

#print axioms stage₃Equiv
#print axioms stage₃Equiv_algebraMap
#print axioms stage₃Equiv_root₁
#print axioms stage₃Equiv_root₂
#print axioms stage₃Equiv_root
#print axioms tensorEquiv

end FourCorner.Multiquadratic.BaseChange
