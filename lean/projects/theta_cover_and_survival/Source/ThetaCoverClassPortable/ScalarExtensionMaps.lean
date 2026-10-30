import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
universe u v w p q n
namespace FourCorner.FPDescent
variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  {P : Type p} [AddCommGroup P] [Module R P]
  {Q : Type q} [AddCommGroup Q] [Module R Q]
  {N : Type n} [AddCommGroup N] [Module R N]

theorem scalarMap_smul (h : A →ₐ[R] B) (a : A) (x : A ⊗[R] Q) :
    h.toLinearMap.rTensor Q (a • x) = h a • h.toLinearMap.rTensor Q x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b q => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Transport an actual linear map between scalar extensions along an actual
algebra homomorphism, using the native tensor universal property. -/
def scalarPush (h : A →ₐ[R] B) (f : A ⊗[R] P →ₗ[A] A ⊗[R] Q) :
    B ⊗[R] P →ₗ[B] B ⊗[R] Q :=
  LinearMap.liftBaseChange B
    ((h.toLinearMap.rTensor Q).comp
      ((f.restrictScalars R).comp (TensorProduct.mk R A P 1)))

@[simp] theorem scalarPush_tmul (h : A →ₐ[R] B)
    (f : A ⊗[R] P →ₗ[A] A ⊗[R] Q) (b : B) (p : P) :
    scalarPush h f (b ⊗ₜ[R] p) = b • h.toLinearMap.rTensor Q (f (1 ⊗ₜ[R] p)) := by
  simp [scalarPush, LinearMap.liftBaseChange_tmul]

theorem scalarPush_rTensor (h : A →ₐ[R] B)
    (f : A ⊗[R] P →ₗ[A] A ⊗[R] Q) (x : A ⊗[R] P) :
    scalarPush h f (h.toLinearMap.rTensor P x) = h.toLinearMap.rTensor Q (f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    rw [LinearMap.rTensor_tmul, scalarPush_tmul]
    change h a • h.toLinearMap.rTensor Q (f (1 ⊗ₜ[R] p)) = _
    rw [← scalarMap_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem scalarPush_id (h : A →ₐ[R] B) :
    scalarPush h (LinearMap.id : A ⊗[R] P →ₗ[A] A ⊗[R] P) = LinearMap.id := by
  ext b p
  simp [TensorProduct.smul_tmul']

theorem scalarPush_comp (h : A →ₐ[R] B)
    (f : A ⊗[R] P →ₗ[A] A ⊗[R] Q) (g : A ⊗[R] Q →ₗ[A] A ⊗[R] N) :
    scalarPush h (g.comp f) = (scalarPush h g).comp (scalarPush h f) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b p =>
    simp only [scalarPush_tmul, LinearMap.comp_apply, map_smul]
    rw [scalarPush_rTensor]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem scalarPush_eq_of_unit (h : A →ₐ[R] B)
    (f g : A ⊗[R] P →ₗ[A] A ⊗[R] Q)
    (hf : ∀ p : P, h.toLinearMap.rTensor Q (f (1 ⊗ₜ[R] p)) =
      h.toLinearMap.rTensor Q (g (1 ⊗ₜ[R] p))) :
    scalarPush h f = scalarPush h g := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b p => simp only [scalarPush_tmul, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Equality on the native unit tensors determines the full natural square. -/
theorem liftBaseChange_compatible (h : A →ₐ[R] B)
    (v : P →ₗ[R] A ⊗[R] Q) (F : B ⊗[R] P →ₗ[B] B ⊗[R] Q)
    (hv : ∀ p : P, h.toLinearMap.rTensor Q (v p) = F (1 ⊗ₜ[R] p)) :
    (h.toLinearMap.rTensor Q).comp ((v.liftBaseChange A).restrictScalars R) =
      (F.restrictScalars R).comp (h.toLinearMap.rTensor P) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a p =>
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      LinearMap.liftBaseChange_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    rw [scalarMap_smul, hv]
    rw [show h a ⊗ₜ[R] p = h a • ((1 : B) ⊗ₜ[R] p) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end FourCorner.FPDescent
