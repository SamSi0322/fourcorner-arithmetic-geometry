import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Maps

/-!
Base change for polynomial coordinate rings obtained by adjoining roots.
Every equivalence below is constructed from the tensor-product and quotient
universal properties; no irreducibility or selected field root is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.AdjoinRootBaseChange

open Polynomial
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension commutes with adjoining a root of any polynomial. -/
def polynomialEquiv (p : R[X]) :
    S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot (p.map (algebraMap R S)) :=
  (AdjoinRoot.tensorAlgEquiv p
    (p.map (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R S S) _ _ (by
      apply Associated.of_eq
      rw [Polynomial.map_map]
      congr 1
      ext r
      simp [Algebra.smul_def]))

@[simp] theorem polynomialEquiv_root (p : R[X]) :
    polynomialEquiv (S := S) p (1 ⊗ₜ[R] AdjoinRoot.root p) =
      AdjoinRoot.root (p.map (algebraMap R S)) := by
  unfold polynomialEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

@[simp] theorem polynomialEquiv_of (p : R[X]) (r : R) :
    polynomialEquiv (S := S) p (1 ⊗ₜ[R] AdjoinRoot.of p r) =
      AdjoinRoot.of (p.map (algebraMap R S)) (algebraMap R S r) := by
  unfold polynomialEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  simp [Algebra.smul_def]

@[simp] theorem polynomialEquiv_scalar (p : R[X]) (s : S) :
    polynomialEquiv (S := S) p (s ⊗ₜ[R] (1 : AdjoinRoot p)) =
      algebraMap S (AdjoinRoot (p.map (algebraMap R S))) s :=
  (polynomialEquiv (S := S) p).commutes s

@[simp] theorem polynomialEquiv_symm_root (p : R[X]) :
    (polynomialEquiv (S := S) p).symm
        (AdjoinRoot.root (p.map (algebraMap R S))) =
      1 ⊗ₜ[R] AdjoinRoot.root p :=
  (polynomialEquiv (S := S) p).symm_apply_eq.mpr (polynomialEquiv_root p).symm

/-- The monic quadratic defining a square-root coordinate. -/
def quadratic (a : R) : R[X] := X ^ 2 - C a

theorem quadratic_monic (a : R) : (quadratic a).Monic :=
  monic_X_pow_sub_C a (by decide)

omit [Algebra R S] in
@[simp] theorem quadratic_map (a : R) (f : R →+* S) :
    (quadratic a).map f = quadratic (f a) := by
  simp [quadratic]

/-- Concrete scalar extension of a square-root coordinate. -/
def quadraticEquiv (a : R) :
    S ⊗[R] AdjoinRoot (quadratic a) ≃ₐ[S]
      AdjoinRoot (quadratic (algebraMap R S a)) :=
  (polynomialEquiv (S := S) (quadratic a)).trans
    (AdjoinRoot.algEquivOfEq S _ _ (quadratic_map a (algebraMap R S)))

@[simp] theorem quadraticEquiv_root (a : R) :
    quadraticEquiv (S := S) a (1 ⊗ₜ[R] AdjoinRoot.root (quadratic a)) =
      AdjoinRoot.root (quadratic (algebraMap R S a)) := by
  simp [quadraticEquiv, AdjoinRoot.algEquivOfEq_root]

@[simp] theorem quadraticEquiv_of (a r : R) :
    quadraticEquiv (S := S) a (1 ⊗ₜ[R] AdjoinRoot.of (quadratic a) r) =
      AdjoinRoot.of (quadratic (algebraMap R S a)) (algebraMap R S r) := by
  simp [quadraticEquiv, AdjoinRoot.coe_algEquivOfEq, AdjoinRoot.algHomOfDvd]

@[simp] theorem quadraticEquiv_scalar (a : R) (s : S) :
    quadraticEquiv (S := S) a (s ⊗ₜ[R] (1 : AdjoinRoot (quadratic a))) =
      algebraMap S (AdjoinRoot (quadratic (algebraMap R S a))) s :=
  (quadraticEquiv (S := S) a).commutes s

section Tower

variable {B T : Type*} [CommRing B] [CommRing T] [Algebra R B] [Algebra S T]

/-- One step of a tower after an already constructed scalar-extension
equivalence of its coefficient ring. The coefficient compatibility is an
equality of actual elements, and the new equivalence is constructed. -/
def quadraticTowerTransport (e : S ⊗[R] B ≃ₐ[S] T) (b : B) (c : T)
    (h : e (1 ⊗ₜ[R] b) = c) :
    S ⊗[R] AdjoinRoot (quadratic b) ≃ₐ[S] AdjoinRoot (quadratic c) :=
  (AdjoinRoot.tensorAlgEquiv (R := R) (T := S)
    (quadratic b) (quadratic (1 ⊗ₜ[R] b)) (by simp [quadratic])).trans
    (AdjoinRoot.mapAlgEquiv e (quadratic (1 ⊗ₜ[R] b)) (quadratic c)
      (by simp [quadratic, h]))

@[simp] theorem quadraticTowerTransport_root (e : S ⊗[R] B ≃ₐ[S] T)
    (b : B) (c : T) (h : e (1 ⊗ₜ[R] b) = c) :
    quadraticTowerTransport e b c h (1 ⊗ₜ[R] AdjoinRoot.root (quadratic b)) =
      AdjoinRoot.root (quadratic c) := by
  unfold quadraticTowerTransport
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

@[simp] theorem quadraticTowerTransport_of (e : S ⊗[R] B ≃ₐ[S] T)
    (b x : B) (c : T) (h : e (1 ⊗ₜ[R] b) = c) :
    quadraticTowerTransport e b c h (1 ⊗ₜ[R] AdjoinRoot.of (quadratic b) x) =
      AdjoinRoot.of (quadratic c) (e (1 ⊗ₜ[R] x)) := by
  unfold quadraticTowerTransport
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of,
    AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  rfl

@[simp] theorem quadraticTowerTransport_algebraMap (e : S ⊗[R] B ≃ₐ[S] T)
    (b x : B) (c : T) (h : e (1 ⊗ₜ[R] b) = c) :
    quadraticTowerTransport e b c h
        (1 ⊗ₜ[R] algebraMap B (AdjoinRoot (quadratic b)) x) =
      algebraMap T (AdjoinRoot (quadratic c)) (e (1 ⊗ₜ[R] x)) :=
  quadraticTowerTransport_of e b x c h

end Tower

#print axioms polynomialEquiv
#print axioms polynomialEquiv_root
#print axioms polynomialEquiv_scalar
#print axioms quadraticEquiv
#print axioms quadraticEquiv_root
#print axioms quadraticTowerTransport
#print axioms quadraticTowerTransport_algebraMap

end FourCorner.AdjoinRootBaseChange
