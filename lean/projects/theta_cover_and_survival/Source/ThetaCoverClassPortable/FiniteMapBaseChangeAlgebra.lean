import ThetaCoverClassPortable.AffineBaseChangeSections
import Mathlib.RingTheory.TensorProduct.Quotient
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open scoped TensorProduct
namespace FourCorner.FiniteMapBaseChange.Algebra
variable {R T A : Type u} [CommRing R] [CommRing T] [CommRing A]
  [Algebra R T] [Algebra R A]

theorem finite_aeval_baseChange (a : A)
    (hf : (Polynomial.aeval a : Polynomial R →ₐ[R] A).toRingHom.Finite) :
    (Polynomial.aeval ((1 : T) ⊗ₜ[R] a) : Polynomial T →ₐ[T] T ⊗[R] A).toRingHom.Finite := by
  let M := T ⊗[R] A
  let z : M := 1 ⊗ₜ[R] a
  letI : Algebra (Polynomial R) A := (Polynomial.aeval a : Polynomial R →ₐ[R] A).toRingHom.toAlgebra
  haveI : IsScalarTower R (Polynomial R) A := IsScalarTower.of_algHom (Polynomial.aeval a)
  haveI : Module.Finite (Polynomial R) A := hf
  letI : Algebra (Polynomial R) (Polynomial T) := (Polynomial.mapRingHom (algebraMap R T)).toAlgebra
  haveI : IsScalarTower R (Polynomial R) (Polynomial T) := IsScalarTower.of_algebraMap_eq (by
    intro r
    simp [Polynomial.algebraMap_apply])
  letI : Algebra (Polynomial T) M := (Polynomial.aeval z : Polynomial T →ₐ[T] M).toRingHom.toAlgebra
  haveI : IsScalarTower T (Polynomial T) M := IsScalarTower.of_algHom (Polynomial.aeval z)
  haveI : IsScalarTower R (Polynomial T) M := IsScalarTower.to₁₃₄ R T (Polynomial T) M
  letI : Algebra (Polynomial R) M :=
    ((algebraMap (Polynomial T) M).comp (algebraMap (Polynomial R) (Polynomial T))).toAlgebra
  letI : SMul (Polynomial R) M := (inferInstance : Algebra (Polynomial R) M).toSMul
  haveI : IsScalarTower (Polynomial R) (Polynomial T) M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R (Polynomial R) M :=
    IsScalarTower.to₁₂₄ R (Polynomial R) (Polynomial T) M
  let j : A →ₐ[R] M := Algebra.TensorProduct.includeRight
  have hx : j (algebraMap (Polynomial R) A Polynomial.X) =
      algebraMap (Polynomial R) M Polynomial.X := by
    change j ((Polynomial.aeval a) Polynomial.X) =
      (Polynomial.aeval z) ((Polynomial.mapRingHom (algebraMap R T)) Polynomial.X)
    simp [z, j]
    rfl
  have hc : j.toRingHom.comp (algebraMap (Polynomial R) A) = algebraMap (Polynomial R) M := by
    have h : j.comp (IsScalarTower.toAlgHom R (Polynomial R) A) =
        IsScalarTower.toAlgHom R (Polynomial R) M := Polynomial.algHom_ext hx
    exact congrArg AlgHom.toRingHom h
  let jP : A →ₐ[Polynomial R] M := { j.toRingHom with commutes' := fun p => RingHom.congr_fun hc p }
  let φ : Polynomial T ⊗[Polynomial R] A →ₐ[Polynomial T] M :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) jP (fun _ _ => .all _ _)
  have hφ (t : T) (x : A) : φ (Polynomial.C t ⊗ₜ[Polynomial R] x) = t ⊗ₜ[R] x := by
    change (Polynomial.aeval z (Polynomial.C t)) * (1 ⊗ₜ[R] x) = t ⊗ₜ[R] x
    rw [Polynomial.aeval_C]
    change (t ⊗ₜ[R] (1 : A)) * ((1 : T) ⊗ₜ[R] x) = t ⊗ₜ[R] x
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hsurj : Function.Surjective φ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero φ⟩
    | tmul t x => exact ⟨Polynomial.C t ⊗ₜ[Polynomial R] x, hφ t x⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add φ x' y'⟩
  exact Module.Finite.of_surjective φ.toLinearMap hsurj

section Fibres
variable {A' S : Type u} [CommRing A'] [CommRing S] [Algebra T A'] [Algebra T S]
  [Algebra R S] [IsScalarTower R T S]

/-- An exact quotient isomorphism preserving the level scalar after arbitrary base change. -/
def fibreEquiv (e : T ⊗[R] A ≃ₐ[T] A') (a : A) (a' : A')
    (ha : e (1 ⊗ₜ[R] a) = a') (s : S) :
    (S ⊗[T] A' ⧸ Ideal.span {(1 : S) ⊗ₜ[T] a' - s ⊗ₜ[T] (1 : A')}) ≃ₐ[S]
    (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) := by
  let E : S ⊗[T] A' ≃ₐ[S] S ⊗[R] A :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e.symm).trans
      (Algebra.TensorProduct.cancelBaseChange R T S S A)
  refine Ideal.quotientEquivAlg _ _ E ?_
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp [E, ← ha, Algebra.TensorProduct.cancelBaseChange_tmul]
  change s ⊗ₜ[R] (1 : A) = (Algebra.TensorProduct.cancelBaseChange R T S S A)
    (s ⊗ₜ[T] ((1 : T) ⊗ₜ[R] (1 : A)))
  rw [Algebra.TensorProduct.cancelBaseChange_tmul]
  simp

/-- All-local-base finite/free/same-rank fibres transfer through the genuine tensor chart. -/
theorem levelSet_free (e : T ⊗[R] A ≃ₐ[T] A') (a : A) (a' : A')
    (ha : e (1 ⊗ₜ[R] a) = a') (m : ℕ)
    (h : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] a - s ⊗ₜ[R] (1 : A)}) = m)
    [IsLocalRing S] (s : S) :
    Module.Finite S (S ⊗[T] A' ⧸ Ideal.span {(1 : S) ⊗ₜ[T] a' - s ⊗ₜ[T] (1 : A')}) ∧
      Module.Free S (S ⊗[T] A' ⧸ Ideal.span {(1 : S) ⊗ₜ[T] a' - s ⊗ₜ[T] (1 : A')}) ∧
      Module.finrank S (S ⊗[T] A' ⧸ Ideal.span {(1 : S) ⊗ₜ[T] a' - s ⊗ₜ[T] (1 : A')}) = m := by
  obtain ⟨hfin, hfree, hrank⟩ := h S s
  let E := (fibreEquiv e a a' ha s).toLinearEquiv
  haveI := hfin
  haveI := hfree
  exact ⟨Module.Finite.equiv E.symm, Module.Free.of_equiv E.symm, E.finrank_eq.trans hrank⟩
end Fibres
end FourCorner.FiniteMapBaseChange.Algebra
