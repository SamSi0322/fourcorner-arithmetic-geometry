import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped TensorProduct

namespace FourCorner.PairCoactionInvariants
variable {K A M N : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- Actual coordinate contraction on the left tensor factor. -/
def coefficient (l : A →ₗ[K] K) : A ⊗[K] M →ₗ[K] M :=
  (TensorProduct.lid K M).toLinearMap.comp (l.rTensor M)

@[simp] theorem coefficient_tmul (l : A →ₗ[K] K) (a : A) (m : M) :
    coefficient l (a ⊗ₜ[K] m)=l a • m := by
  simp [coefficient]

theorem coefficient_natural (l : A →ₗ[K] K) (f : M →ₗ[K] N)
    (z : A ⊗[K] M) :
    coefficient l (TensorProduct.map (LinearMap.id : A →ₗ[K] A) f z)=
      f (coefficient l z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp [hx, hy]

/-- Tensor coordinates separate every actual nonzero tensor. This does
not need a finite-dimensional or reducedness assumption. -/
theorem exists_nonzero_coefficient (z : A ⊗[K] M) (hz : z≠0) :
    ∃ l : A →ₗ[K] K, coefficient l z≠0 := by
  classical
  let b := Module.Free.chooseBasis K A
  by_contra h
  push Not at h
  apply hz
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
  simpa [coefficient] using h (b.coord i)

def unitVector (a0 : A) : M →ₗ[K] A ⊗[K] M := TensorProduct.mk K A M a0

/-- The pair-descent coassociativity equation forces each coordinate of
rho(m) to be an actual invariant in M. -/
theorem coefficient_invariant (a0 : A) (rho : M →ₗ[K] A ⊗[K] M)
    (hco : ∀ m, TensorProduct.map (LinearMap.id : A →ₗ[K] A) rho (rho m)=
      TensorProduct.map (LinearMap.id : A →ₗ[K] A) (unitVector a0) (rho m))
    (l : A →ₗ[K] K) (m : M) :
    rho (coefficient l (rho m))=a0 ⊗ₜ[K] coefficient l (rho m) := by
  have h := congrArg (coefficient (M:=A ⊗[K] M) l) (hco m)
  simpa only [coefficient_natural, unitVector, TensorProduct.mk_apply] using h

theorem exists_nonzero_invariant_of_injective (a0 : A)
    (rho : M →ₗ[K] A ⊗[K] M) (hrho : Function.Injective rho)
    (hco : ∀ m, TensorProduct.map (LinearMap.id : A →ₗ[K] A) rho (rho m)=
      TensorProduct.map (LinearMap.id : A →ₗ[K] A) (unitVector a0) (rho m))
    {m : M} (hm : m≠0) : ∃ w : M, w≠0 ∧ rho w=a0 ⊗ₜ[K] w := by
  have hrm : rho m≠0 := by
    intro h
    apply hm
    exact hrho (by simpa using h)
  obtain ⟨l, hl⟩ := exists_nonzero_coefficient (rho m) hrm
  exact ⟨coefficient l (rho m), hl, coefficient_invariant a0 rho hco l m⟩

/-- The usual genuine counit identity supplies injectivity. The actual
groupoid application must construct this rho, coassociativity and counit;
the existence of an invariant is NOT an input. -/
theorem exists_nonzero_invariant_of_counit (a0 : A)
    (rho : M →ₗ[K] A ⊗[K] M) (mu : A ⊗[K] M →ₗ[K] M)
    (hcounit : ∀ m, mu (rho m)=m)
    (hco : ∀ m, TensorProduct.map (LinearMap.id : A →ₗ[K] A) rho (rho m)=
      TensorProduct.map (LinearMap.id : A →ₗ[K] A) (unitVector a0) (rho m))
    {m : M} (hm : m≠0) : ∃ w : M, w≠0 ∧ rho w=a0 ⊗ₜ[K] w :=
  exists_nonzero_invariant_of_injective a0 rho
    (Function.LeftInverse.injective hcounit) hco hm

#print axioms coefficient_invariant
#print axioms exists_nonzero_invariant_of_injective
#print axioms exists_nonzero_invariant_of_counit
end FourCorner.PairCoactionInvariants
