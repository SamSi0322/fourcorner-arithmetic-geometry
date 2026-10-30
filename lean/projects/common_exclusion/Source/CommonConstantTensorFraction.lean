import CommonConstantTensorInjection

noncomputable section
namespace FourCorner.CommonConstantTensorFraction
open scoped TensorProduct
open Polynomial
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def fractionAlgebra : Algebra (L ⊗[K] RatFunc K) (RatFunc L) :=
  (CommonConstantTensorInjection.tensorMap K L).toRingHom.toAlgebra

theorem isFractionRing :
    letI := fractionAlgebra K L
    IsFractionRing (L ⊗[K] RatFunc K) (RatFunc L) := by
  letI := fractionAlgebra K L
  letI : FaithfulSMul (L ⊗[K] RatFunc K) (RatFunc L) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (CommonConstantTensorInjection.tensorMap_injective K L)
  let j : L ⊗[K] K[X] →ₐ[K] L ⊗[K] RatFunc K :=
    Algebra.TensorProduct.map (AlgHom.id K L) (IsScalarTower.toAlgHom K K[X] (RatFunc K))
  have hj (p : L[X]) : CommonConstantTensorInjection.tensorMap K L
      (j ((polyEquivTensor' K L) p)) = algebraMap L[X] (RatFunc L) p := by
    have h := RingHom.congr_fun (CommonConstantTensorInjection.tensorMap_base K L)
      ((polyEquivTensor' K L) p)
    change CommonConstantTensorInjection.tensorMap K L (j ((polyEquivTensor' K L) p)) =
      algebraMap L[X] (RatFunc L) ((polyEquivTensor' K L).symm ((polyEquivTensor' K L) p)) at h
    rw [AlgEquiv.symm_apply_apply] at h
    exact h

  apply IsFractionRing.of_field
  intro z
  refine ⟨j ((polyEquivTensor' K L) z.num),j ((polyEquivTensor' K L) z.denom),?_⟩
  change z = CommonConstantTensorInjection.tensorMap K L _ /
    CommonConstantTensorInjection.tensorMap K L _
  rw [hj,hj]
  exact (RatFunc.num_div_denom z).symm

#print axioms isFractionRing
end FourCorner.CommonConstantTensorFraction
