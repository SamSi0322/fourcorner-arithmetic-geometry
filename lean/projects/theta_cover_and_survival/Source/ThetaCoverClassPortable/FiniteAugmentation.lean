import ThetaCoverClassPortable.Augmentation
import Mathlib.LinearAlgebra.TensorProduct.Prod
import ThetaCoverClassPortable.KernelBaseChange
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Flat.EquationalCriterion

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
universe u
namespace FourCorner.EulerAugmentation
variable {R C0 C1 Q : Type u} [CommRing R]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup Q] [Module R Q]

theorem flat_prod (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P U _ _ _ _ f hf
  have hM := Module.Flat.rTensor_preserves_injective_linearMap (M := M) f hf
  have hN := Module.Flat.rTensor_preserves_injective_linearMap (M := N) f hf
  have hsq (x : P ⊗[R] (M × N)) :
      TensorProduct.prodRight R R U M N (f.rTensor (M × N) x) =
        ((f.rTensor M).prodMap (f.rTensor N)) (TensorProduct.prodRight R R P M N x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul p mn => simp [LinearMap.rTensor_tmul,TensorProduct.prodRight_tmul]
    | add x y hx hy => simp only [map_add,hx,hy]
  intro x y h
  apply (TensorProduct.prodRight R R P M N).injective
  apply hM.prodMap hN
  exact (hsq x).symm.trans ((congrArg (TensorProduct.prodRight R R U M N) h).trans (hsq y))

/-- Noetherianity gives finiteness of the ACTUAL augmented kernel from the
original kernel and finite Q; the original modules may be infinite. -/
theorem finite_augmented_kernel [IsNoetherianRing R] (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R Q] :
    Module.Finite R (LinearMap.ker (augment d f)) := by
  let b := boundary d f
  haveI : Module.Finite R (LinearMap.ker b) := Module.Finite.equiv (kernelBoundaryEquiv d f)
  haveI : Module.Finite R (LinearMap.range b) := inferInstance
  haveI : Module.Finite R ((LinearMap.ker (augment d f)) ⧸ LinearMap.ker b) :=
    Module.Finite.equiv b.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker b)

/-- Finite cokernel constructs a literal finite-free augmentation with true
surjectivity. Only the auxiliary finite-free Q is projective. -/
theorem exists_surjective_augmentation (d : C0 →ₗ[R] C1)
    [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] C1), Function.Surjective (augment d f) := by
  obtain ⟨n,q,hq⟩ := Module.Finite.exists_fin' R (C1 ⧸ LinearMap.range d)
  let π := (LinearMap.range d).mkQ
  obtain ⟨f,hf⟩ := Module.projective_lifting_property π q (Submodule.mkQ_surjective _)
  refine ⟨n,f,?_⟩
  intro y
  obtain ⟨v,hv⟩ := hq (π y)
  have hfv : π (f v)=q v := LinearMap.congr_fun hf v
  have hm : y-f v ∈ LinearMap.range d := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change π (y-f v)=0
    rw [map_sub,hfv,hv,sub_self]
  obtain ⟨c,hc⟩ := hm
  refine ⟨(c,v),?_⟩
  change d c+f v=y
  rw [hc,sub_add_cancel]

/-- True flatness/projectivity of the actual kernel of the constructed
surjection. No original chart projectivity/freeness is assumed. -/
theorem projective_augmented_kernel [IsNoetherianRing R]
    [Module.Flat R C0] [Module.Flat R C1] [Module.Flat R Q]
    (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R Q]
    (ha : Function.Surjective (augment d f)) :
    Module.Projective R (LinearMap.ker (augment d f)) := by
  haveI : Module.Flat R (C0 × Q) := flat_prod C0 Q
  haveI : Module.Flat R (LinearMap.ker (augment d f)) :=
    FourCorner.MumfordKernel.flat_kernel (augment d f) ha
  haveI := finite_augmented_kernel d f
  haveI : Module.FinitePresentation R (LinearMap.ker (augment d f)) :=
    Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation
end FourCorner.EulerAugmentation
