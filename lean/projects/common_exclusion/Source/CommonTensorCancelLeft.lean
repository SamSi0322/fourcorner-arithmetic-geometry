import CommonTensorFlat

noncomputable section
namespace FourCorner.CommonTensorCancelLeft
open scoped TensorProduct
variable (K F L E : Type*) [Field K] [Field F] [Field L] [Field E]
  [Algebra K F] [Algebra K L] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

def equiv : (L ⊗[K] F) ⊗[F] E ≃ₐ[L] L ⊗[K] E := by
  let e : (L ⊗[K] F) ⊗[F] E ≃+* L ⊗[K] E :=
    (Algebra.TensorProduct.comm F (L ⊗[K] F) E).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E)
        (Algebra.TensorProduct.commRight K F L).symm).toRingEquiv.trans
        ((Algebra.TensorProduct.cancelBaseChange K F E E L).toRingEquiv.trans
          (Algebra.TensorProduct.comm K E L).toRingEquiv))
  refine { e with commutes' := ?_ }
  intro l
  change e ((l ⊗ₜ[K] (1:F)) ⊗ₜ[F] (1:E)) = l ⊗ₜ[K] (1:E)
  simp [e,Algebra.TensorProduct.cancelBaseChange_tmul]

#print axioms equiv
end FourCorner.CommonTensorCancelLeft
