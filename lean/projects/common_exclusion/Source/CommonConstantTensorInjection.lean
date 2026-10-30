import CommonConstantMap
import CommonTensorLocalization
import Mathlib.RingTheory.PolynomialAlgebra

noncomputable section
namespace FourCorner.CommonConstantTensorInjection
open scoped TensorProduct
open Polynomial
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

def ratAlgHom : RatFunc K →ₐ[K] RatFunc L where
  __ := CommonConstantMap.ratMap K L
  commutes' a := by
    change CommonConstantMap.ratMap K L (algebraMap K (RatFunc K) a) = _
    rw [CommonConstantMap.ratMap_constant]
    exact (IsScalarTower.algebraMap_apply K L (RatFunc L) a).symm

def tensorMap : L ⊗[K] RatFunc K →ₐ[L] RatFunc L :=
  Algebra.TensorProduct.lift (Algebra.ofId L (RatFunc L)) (ratAlgHom K L)
    (fun _ _ => Commute.all _ _)

theorem tensorMap_base : (tensorMap K L).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id K L)
        (IsScalarTower.toAlgHom K K[X] (RatFunc K))).toRingHom =
      (algebraMap L[X] (RatFunc L)).comp (polyEquivTensor' K L).symm.toRingHom := by
  apply RingHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l p =>
    simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Algebra.TensorProduct.map_tmul,AlgHom.id_apply,IsScalarTower.coe_toAlgHom,
      tensorMap,Algebra.TensorProduct.lift_tmul]
    change algebraMap L (RatFunc L) l *
      CommonConstantMap.ratMap K L (algebraMap K[X] (RatFunc K) p) = _
    rw [CommonConstantMap.ratMap_polynomial]
    simp [coe_polyEquivTensor'_symm,polyEquivTensor_symm_apply_tmul_eq_smul,
      Algebra.smul_def]
  | add x y hx hy => simpa only [map_add,hx,hy]

theorem tensorMap_injective : Function.Injective (tensorMap K L) := by
  apply CommonTensorLocalization.map_injective_of_base_injective K K[X] (RatFunc K) L
    (RatFunc L) (tensorMap K L).toRingHom
  rw [tensorMap_base K L]
  exact (RatFunc.algebraMap_injective (K:=L)).comp (polyEquivTensor' K L).symm.injective

#print axioms tensorMap_injective
end FourCorner.CommonConstantTensorInjection
