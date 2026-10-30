import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.IdealFlatDescent
open Algebra.TensorProduct

/-- Flatness preserves the actual kernel for arbitrary algebra maps; unlike
right exactness alone, no surjectivity of g is required. -/
theorem tensor_kernel_of_flat {R A B C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Module.Flat R A]
    (g : B →ₐ[R] C) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) g).toRingHom =
      (RingHom.ker g.toRingHom).map
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom := by
  rw [← Submodule.restrictScalars_inj R]
  have h : (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) g).toRingHom).restrictScalars R =
      LinearMap.ker (LinearMap.lTensor A g.toLinearMap) := rfl
  rw [h]
  change LinearMap.ker (LinearMap.lTensor A g.toLinearMap) =
    ((RingHom.ker g.toRingHom).map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)).restrictScalars R
  rw [Ideal.map_includeRight_eq]
  exact (Module.Flat.lTensor_exact A g.toLinearMap.exact_subtype_ker_map).linearMap_ker_eq

end FourCorner.IdealFlatDescent
#print axioms FourCorner.IdealFlatDescent.tensor_kernel_of_flat
