import Mathlib.Algebra.Colimit.Module

/-! Concrete colimit data for a directed system of actual modules.
The surjectivity and eventual-zero fields are the ordinary direct-limit
criterion; they do not assert descent of any linear map or equivalence. -/
universe u v w z

namespace FourCorner.FPDescent

variable (R : Type u) [CommRing R]
  (ι : Type v) [Preorder ι]
  (G : ι → Type w) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
  (M : Type z) [AddCommGroup M] [Module R M]

structure ModuleColimitWitness where
  incl : ∀ i, G i →ₗ[R] M
  comm : ∀ (i j : ι) (h : i ≤ j), (incl j).comp (f i j h) = incl i
  surj : ∀ x : M, ∃ (i : ι) (y : G i), incl i y = x
  vanish : ∀ (i : ι) (x : G i), incl i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0

end FourCorner.FPDescent
