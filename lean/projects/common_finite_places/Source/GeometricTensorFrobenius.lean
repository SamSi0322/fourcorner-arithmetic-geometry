import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
open scoped TensorProduct
namespace FourCorner.GeometricTensorFrobenius
variable (k L F : Type*) [Field k] [Fintype k] [Field L] [Field F]
  [Algebra k L] [Algebra k F]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Frobenius acts on the original finite-constant function field and fixes
the geometric constants in the ACTUAL tensor product. -/
def tensorFrobenius : (L ⊗[k] F) →ₐ[L] (L ⊗[k] F) :=
  Algebra.TensorProduct.lift (Algebra.ofId L (L ⊗[k] F))
    ((Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).comp
      (FiniteField.frobeniusAlgHom k F)) (fun _ _ => Commute.all _ _)

theorem tensorFrobenius_tmul (l : L) (x : F) :
    tensorFrobenius k L F (l ⊗ₜ[k] x) = l ⊗ₜ[k] (x^(Fintype.card k)) := by
  simp only [tensorFrobenius,Algebra.TensorProduct.lift_tmul,AlgHom.comp_apply,
    FiniteField.coe_frobeniusAlgHom,Algebra.TensorProduct.includeRight_apply,
    Algebra.ofId_apply,Algebra.TensorProduct.algebraMap_apply,Algebra.algebraMap_self_apply]
  change (l ⊗ₜ[k] (1 : F)) * ((1 : L) ⊗ₜ[k] (x^(Fintype.card k))) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

theorem tensorFrobenius_injective : Function.Injective (tensorFrobenius k L F) := by
  let f := FiniteField.frobeniusAlgHom k F
  have hinj : Function.Injective (f.toLinearMap.lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.toLinearMap f.injective
  have heq (a : L ⊗[k] F) : f.toLinearMap.lTensor L a = tensorFrobenius k L F a := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul l x =>
      rw [LinearMap.lTensor_tmul,tensorFrobenius_tmul]
      simp only [f,AlgHom.toLinearMap_apply,FiniteField.coe_frobeniusAlgHom]
    | add a b ha hb => simp only [map_add,ha,hb]
  intro a b h
  apply hinj
  rw [heq,heq]
  exact h

variable [IsDomain (L ⊗[k] F)]

def fractionFrobenius : FractionRing (L ⊗[k] F) →+* FractionRing (L ⊗[k] F) :=
  IsFractionRing.lift (K := FractionRing (L ⊗[k] F))
    (g := (algebraMap (L ⊗[k] F) (FractionRing (L ⊗[k] F))).comp
      (tensorFrobenius k L F).toRingHom)
    ((IsFractionRing.injective (L ⊗[k] F) (FractionRing (L ⊗[k] F))).comp
      (tensorFrobenius_injective k L F))

theorem fractionFrobenius_algebraMap (a : L ⊗[k] F) :
    fractionFrobenius k L F (algebraMap (L ⊗[k] F) (FractionRing (L ⊗[k] F)) a) =
      algebraMap (L ⊗[k] F) (FractionRing (L ⊗[k] F)) (tensorFrobenius k L F a) :=
  IsFractionRing.lift_algebraMap _ a

/-- The actual fraction-field Frobenius is geometric-constant linear. -/
def geometricFrobenius : FractionRing (L ⊗[k] F) →ₐ[L] FractionRing (L ⊗[k] F) where
  __ := fractionFrobenius k L F
  commutes' l := by
    change fractionFrobenius k L F (algebraMap L (FractionRing (L ⊗[k] F)) l) = _
    rw [IsScalarTower.algebraMap_apply L (L ⊗[k] F) (FractionRing (L ⊗[k] F)),
      fractionFrobenius_algebraMap,(tensorFrobenius k L F).commutes]

def sourceInclusion : F →ₐ[k] FractionRing (L ⊗[k] F) :=
  (IsScalarTower.toAlgHom k (L ⊗[k] F) (FractionRing (L ⊗[k] F))).comp
    Algebra.TensorProduct.includeRight

/-- The defining geometric Frobenius square holds on EVERY original field
element, with no Frobenius or point-count datum assumed. -/
theorem geometricFrobenius_source (x : F) :
    geometricFrobenius k L F (sourceInclusion k L F x) =
      sourceInclusion k L F (x^(Fintype.card k)) := by
  change fractionFrobenius k L F
    (algebraMap (L ⊗[k] F) (FractionRing (L ⊗[k] F)) ((1 : L) ⊗ₜ[k] x)) = _
  rw [fractionFrobenius_algebraMap,tensorFrobenius_tmul]
  simp only [sourceInclusion,AlgHom.comp_apply,IsScalarTower.toAlgHom_apply,
    Algebra.TensorProduct.includeRight_apply]

end FourCorner.GeometricTensorFrobenius
#print axioms FourCorner.GeometricTensorFrobenius.tensorFrobenius_injective
#print axioms FourCorner.GeometricTensorFrobenius.geometricFrobenius_source
