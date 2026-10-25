import geometry.MultiquadraticBaseChange
import Mathlib.RingTheory.PolynomialAlgebra

/-!
The actual three-coordinate algebra over a polynomial ring commutes with
extension of its constant ring. In particular this supplies the tensor-product
bridge needed when extending constants from `ℚ` to an algebraic closure.
-/

noncomputable section
namespace FourCorner.Multiquadratic.BaseChange

open Polynomial CoordinateAlgebra
open scoped TensorProduct

section Reindex
variable {A S R T : Type*}
  [CommRing A] [CommRing S] [CommRing R] [CommRing T]
  [Algebra A S] [Algebra A R] [Algebra S T]

/-- The generic tower equivalence with explicitly named target radicands. -/
def stage₃EquivOfImages (e : S ⊗[A] R ≃ₐ[S] T) (a b c : R) (a' b' c' : T)
    (ha : e (1 ⊗ₜ[A] a) = a') (hb : e (1 ⊗ₜ[A] b) = b')
    (hc : e (1 ⊗ₜ[A] c) = c') :
    S ⊗[A] Stage₃ R a b c ≃ₐ[S] Stage₃ T a' b' c' := by
  subst a' b' c'
  exact stage₃Equiv e a b c

@[simp] theorem stage₃EquivOfImages_algebraMap
    (e : S ⊗[A] R ≃ₐ[S] T) (a b c x : R) (a' b' c' : T)
    (ha : e (1 ⊗ₜ[A] a) = a') (hb : e (1 ⊗ₜ[A] b) = b')
    (hc : e (1 ⊗ₜ[A] c) = c') :
    stage₃EquivOfImages e a b c a' b' c' ha hb hc
        (1 ⊗ₜ[A] algebraMap R (Stage₃ R a b c) x) =
      algebraMap T (Stage₃ T a' b' c') (e (1 ⊗ₜ[A] x)) := by
  subst a' b' c'
  exact stage₃Equiv_algebraMap e a b c x

@[simp] theorem stage₃EquivOfImages_root
    (e : S ⊗[A] R ≃ₐ[S] T) (a b c : R) (a' b' c' : T)
    (ha : e (1 ⊗ₜ[A] a) = a') (hb : e (1 ⊗ₜ[A] b) = b')
    (hc : e (1 ⊗ₜ[A] c) = c') :
    stage₃EquivOfImages e a b c a' b' c' ha hb hc
        (1 ⊗ₜ[A] AdjoinRoot.root (equation₃ R a b c)) =
      AdjoinRoot.root (equation₃ T a' b' c') := by
  subst a' b' c'
  exact stage₃Equiv_root e a b c

@[simp] theorem stage₃EquivOfImages_coordinate₁
    (e : S ⊗[A] R ≃ₐ[S] T) (a b c : R) (a' b' c' : T)
    (ha : e (1 ⊗ₜ[A] a) = a') (hb : e (1 ⊗ₜ[A] b) = b')
    (hc : e (1 ⊗ₜ[A] c) = c') :
    stage₃EquivOfImages e a b c a' b' c' ha hb hc
        (1 ⊗ₜ[A] coordinate₁ R a b c) = coordinate₁ T a' b' c' := by
  subst a' b' c'
  exact stage₃Equiv_root₁ e a b c

@[simp] theorem stage₃EquivOfImages_coordinate₂
    (e : S ⊗[A] R ≃ₐ[S] T) (a b c : R) (a' b' c' : T)
    (ha : e (1 ⊗ₜ[A] a) = a') (hb : e (1 ⊗ₜ[A] b) = b')
    (hc : e (1 ⊗ₜ[A] c) = c') :
    stage₃EquivOfImages e a b c a' b' c' ha hb hc
        (1 ⊗ₜ[A] coordinate₂ R a b c) = coordinate₂ T a' b' c' := by
  subst a' b' c'
  exact stage₃Equiv_root₂ e a b c

end Reindex

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- Extension of constants on the actual polynomial coordinate algebra. -/
def polynomialCoordinateEquiv (a b c : A[X]) :
    S ⊗[A] Stage₃ A[X] a b c ≃ₐ[S]
      Stage₃ S[X] (a.map (algebraMap A S)) (b.map (algebraMap A S))
        (c.map (algebraMap A S)) :=
  stage₃EquivOfImages (polyEquivTensor' A S).symm a b c
    (a.map (algebraMap A S)) (b.map (algebraMap A S)) (c.map (algebraMap A S))
    (by simp) (by simp) (by simp)

/-- Every polynomial coefficient is transported by its coefficient map. -/
@[simp] theorem polynomialCoordinateEquiv_algebraMap (a b c p : A[X]) :
    polynomialCoordinateEquiv (S := S) a b c
        (1 ⊗ₜ[A] algebraMap A[X] (Stage₃ A[X] a b c) p) =
      algebraMap S[X]
        (Stage₃ S[X] (a.map (algebraMap A S)) (b.map (algebraMap A S))
          (c.map (algebraMap A S))) (p.map (algebraMap A S)) := by
  simp [polynomialCoordinateEquiv]

/-- The projection coordinate `Z` is preserved under extension of constants. -/
@[simp] theorem polynomialCoordinateEquiv_parameter (a b c : A[X]) :
    polynomialCoordinateEquiv (S := S) a b c
        (1 ⊗ₜ[A] algebraMap A[X] (Stage₃ A[X] a b c) X) =
      algebraMap S[X]
        (Stage₃ S[X] (a.map (algebraMap A S)) (b.map (algebraMap A S))
          (c.map (algebraMap A S))) X := by
  simp

@[simp] theorem polynomialCoordinateEquiv_root (a b c : A[X]) :
    polynomialCoordinateEquiv (S := S) a b c
        (1 ⊗ₜ[A] AdjoinRoot.root (equation₃ A[X] a b c)) =
      AdjoinRoot.root (equation₃ S[X]
        (a.map (algebraMap A S)) (b.map (algebraMap A S)) (c.map (algebraMap A S))) := by
  simp [polynomialCoordinateEquiv]

@[simp] theorem polynomialCoordinateEquiv_coordinate₁ (a b c : A[X]) :
    polynomialCoordinateEquiv (S := S) a b c (1 ⊗ₜ[A] coordinate₁ A[X] a b c) =
      coordinate₁ S[X] (a.map (algebraMap A S)) (b.map (algebraMap A S))
        (c.map (algebraMap A S)) := by
  simp [polynomialCoordinateEquiv]

@[simp] theorem polynomialCoordinateEquiv_coordinate₂ (a b c : A[X]) :
    polynomialCoordinateEquiv (S := S) a b c (1 ⊗ₜ[A] coordinate₂ A[X] a b c) =
      coordinate₂ S[X] (a.map (algebraMap A S)) (b.map (algebraMap A S))
        (c.map (algebraMap A S)) := by
  simp [polynomialCoordinateEquiv]

@[simp] theorem polynomialCoordinateEquiv_coordinate₃ (a b c : A[X]) :
    polynomialCoordinateEquiv (S := S) a b c (1 ⊗ₜ[A] coordinate₃ A[X] a b c) =
      coordinate₃ S[X] (a.map (algebraMap A S)) (b.map (algebraMap A S))
        (c.map (algebraMap A S)) :=
  polynomialCoordinateEquiv_root a b c

@[simp] theorem polynomialCoordinateEquiv_scalar (a b c : A[X]) (s : S) :
    polynomialCoordinateEquiv (S := S) a b c (s ⊗ₜ[A] (1 : Stage₃ A[X] a b c)) =
      algebraMap S
        (Stage₃ S[X] (a.map (algebraMap A S)) (b.map (algebraMap A S))
          (c.map (algebraMap A S))) s :=
  (polynomialCoordinateEquiv (S := S) a b c).commutes s

#print axioms polynomialCoordinateEquiv
#print axioms polynomialCoordinateEquiv_parameter
#print axioms polynomialCoordinateEquiv_root
#print axioms polynomialCoordinateEquiv_coordinate₁
#print axioms polynomialCoordinateEquiv_coordinate₂

end FourCorner.Multiquadratic.BaseChange
