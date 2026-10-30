import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Tensor

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FourCorner.MumfordKernel
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R]
variable {C0 C1 : Type v} [AddCommGroup C0] [AddCommGroup C1] [Module R C0] [Module R C1]

private theorem tensor_kernel_injective_of_flat_cover [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (hd : Function.Surjective d)
    {F : Type w} {N : Type*} [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup N] [Module R N] (q : F →ₗ[R] N) (hq : Function.Surjective q) :
    Function.Injective ((LinearMap.ker d).subtype.lTensor N) := by
  have hfinj : Function.Injective ((LinearMap.ker q).subtype.rTensor C1) :=
    Module.Flat.rTensor_preserves_injective_linearMap (LinearMap.ker q).subtype Subtype.val_injective
  have hginj : Function.Injective ((LinearMap.ker d).subtype.lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap (LinearMap.ker d).subtype Subtype.val_injective
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (R:=R) (M₁:=LinearMap.ker q) (M₂:=F) (M₃:=N) (N₁:=LinearMap.ker d) (N₂:=C0) (N₃:=C1)
    (f₁:=(LinearMap.ker q).subtype) (f₂:=q) (g₁:=(LinearMap.ker d).subtype) (g₂:=d)
    q.exact_subtype_ker_map hq d.exact_subtype_ker_map hd hfinj hginj

/-- Flat TARGET and true surjectivity imply that the original kernel
inclusion stays injective after tensoring with ANY module N. Only the
actual canonical auxiliary presentation of N is free, not C0 or C1. -/
theorem tensor_kernel_subtype_injective [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (hd : Function.Surjective d)
    (N : Type w) [AddCommGroup N] [Module R N] :
    Function.Injective ((LinearMap.ker d).subtype.lTensor N) := by
  let q : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R (fun n : N=>n)
  have hq : Function.Surjective q := by
    intro n
    refine ⟨Finsupp.single n 1,?_⟩
    exact (Finsupp.linearCombination_single R (v:=fun n : N=>n) 1 n).trans (one_smul R n)
  exact tensor_kernel_injective_of_flat_cover d hd q hq

/-- Kernel of a true surjection between flat modules is actually flat.
This is DERIVED using the universal injectivity above and flatness of C0,
not a pure/split/exact-after-basechange hypothesis. -/
theorem flat_kernel [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (hd : Function.Surjective d) : Module.Flat R (LinearMap.ker d) := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I x y hxy
  apply tensor_kernel_subtype_injective d hd I
  apply (Module.Flat.rTensor_preserves_injective_linearMap (M:=C0) I.subtype I.subtype_injective)
  have hs (z : I ⊗[R] LinearMap.ker d) :
      I.subtype.rTensor C0 ((LinearMap.ker d).subtype.lTensor I z)=
        (LinearMap.ker d).subtype.lTensor R (I.subtype.rTensor (LinearMap.ker d) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a k => rfl
    | add z w hz hw => simp only [map_add,hz,hw]
  exact (hs x).trans ((congrArg ((LinearMap.ker d).subtype.lTensor R) hxy).trans (hs y).symm)

#print axioms tensor_kernel_subtype_injective
#print axioms flat_kernel
end
end FourCorner.MumfordKernel
