import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Descent of geometric-fibre non-zero-divisors along the actual algebraic-closure map. -/

universe u v w

open scoped TensorProduct nonZeroDivisors

namespace FourCorner.GeometricFibres

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Flat A B]

/-- Tensoring the canonical embedding into an algebraic closure with the flat A-module B
preserves injectivity. Both sides are the actual tensor products over A. -/
theorem tensor_algebraicClosure_injective (K : Type w) [Field K] [Algebra A K] :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id A B)
      (IsScalarTower.toAlgHom A K (AlgebraicClosure K))) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := B)
    (IsScalarTower.toAlgHom A K (AlgebraicClosure K)).toLinearMap
    (RingHom.injective (algebraMap K (AlgebraicClosure K)))
  exact h

/-- Regularity over the algebraic closure descends through the canonical injective map. -/
theorem field_regular_of_algebraicClosure (g : B) (K : Type w) [Field K] [Algebra A K]
    (hg : g ⊗ₜ[A] (1 : AlgebraicClosure K) ∈ nonZeroDivisors (B ⊗[A] AlgebraicClosure K)) :
    g ⊗ₜ[A] (1 : K) ∈ nonZeroDivisors (B ⊗[A] K) := by
  apply mem_nonZeroDivisors_of_injective (tensor_algebraicClosure_injective (B := B) K)
  simpa using hg

/-- All algebraically closed A-fields in A's universe suffice for every actual residue field. -/
theorem residueField_regular (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      g ⊗ₜ[A] (1 : K) ∈ nonZeroDivisors (B ⊗[A] K))
    (p : Ideal A) [p.IsPrime] :
    g ⊗ₜ[A] (1 : p.ResidueField) ∈ nonZeroDivisors (B ⊗[A] p.ResidueField) := by
  exact field_regular_of_algebraicClosure g p.ResidueField (hg (AlgebraicClosure p.ResidueField))

/-- The same hypothesis gives regularity over any A-field in that universe. -/
theorem field_regular (g : B)
    (hg : ∀ (L : Type w) [Field L] [IsAlgClosed L] [Algebra A L],
      g ⊗ₜ[A] (1 : L) ∈ nonZeroDivisors (B ⊗[A] L))
    (K : Type w) [Field K] [Algebra A K] :
    g ⊗ₜ[A] (1 : K) ∈ nonZeroDivisors (B ⊗[A] K) := by
  exact field_regular_of_algebraicClosure g K (hg (AlgebraicClosure K))

end FourCorner.GeometricFibres
