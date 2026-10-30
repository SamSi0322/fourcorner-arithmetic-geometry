import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic

noncomputable section
namespace FourCorner.CommonTensorFlat
open scoped TensorProduct
variable {K F L G E : Type*} [Field K] [Field F] [Field L] [Field G] [Field E]
  [Algebra K F] [Algebra K L] [Algebra F G] [Algebra F E]
  [Algebra K E] [IsScalarTower K F E]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem constant_tensor_isDomain_of_rational_tensor_domain
    (f : L ⊗[K] F →ₐ[F] G) (hf : Function.Injective f)
    [IsDomain (G ⊗[F] E)] : IsDomain (L ⊗[K] E) := by
  have hinj : Function.Injective (f.toLinearMap.rTensor E) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  let φ : (L ⊗[K] F) ⊗[F] E →ₐ[F] G ⊗[F] E :=
    Algebra.TensorProduct.map f (AlgHom.id F E)
  have hφ : Function.Injective φ := hinj
  have : IsDomain ((L ⊗[K] F) ⊗[F] E) := Function.Injective.isDomain φ hφ
  let e : (L ⊗[K] F) ⊗[F] E ≃+* L ⊗[K] E :=
    (Algebra.TensorProduct.comm F (L ⊗[K] F) E).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E)
        (Algebra.TensorProduct.commRight K F L).symm).toRingEquiv.trans
        ((Algebra.TensorProduct.cancelBaseChange K F E E L).toRingEquiv.trans
          (Algebra.TensorProduct.comm K E L).toRingEquiv))
  exact Function.Injective.isDomain e.symm e.symm.injective

#print axioms constant_tensor_isDomain_of_rational_tensor_domain
end FourCorner.CommonTensorFlat
