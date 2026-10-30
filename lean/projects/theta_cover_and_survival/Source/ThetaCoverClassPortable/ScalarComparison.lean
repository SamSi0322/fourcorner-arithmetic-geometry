import ThetaCoverClassPortable.Augmentation
import ThetaCoverClassPortable.KernelBaseChange
import Mathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
universe u
namespace FourCorner.EulerAugmentation

section KernelCongr
variable {R M N T : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup T] [Module R T]

def kernelSourceEquiv (a : M →ₗ[R] T) (b : N →ₗ[R] T) (e : M ≃ₗ[R] N)
    (h : b.comp e.toLinearMap=a) : LinearMap.ker a ≃ₗ[R] LinearMap.ker b where
  toFun x := ⟨e x.val,(LinearMap.congr_fun h x.val).trans x.property⟩
  invFun y := ⟨e.symm y.val,by
    have hh := LinearMap.congr_fun h (e.symm y.val)
    change b (e (e.symm y.val))=a (e.symm y.val) at hh
    rw [e.apply_symm_apply] at hh
    exact hh.symm.trans y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' r x := Subtype.ext (map_smul e r x.val)
end KernelCongr

variable {R C0 C1 Q : Type u} [CommRing R]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup Q] [Module R Q]

def tensorPairEquiv (S : Type u) [CommRing S] [Algebra R S] :
    S ⊗[R] (C0 × Q) ≃ₗ[S] (S ⊗[R] C0) × (S ⊗[R] Q) :=
  TensorProduct.prodRight R S S C0 Q

theorem augment_baseChange_comm (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1)
    (S : Type u) [CommRing S] [Algebra R S] :
    (augment (d.baseChange S) (f.baseChange S)).comp (tensorPairEquiv (R := R) (C0 := C0) (Q := Q) S).toLinearMap =
      (augment d f).baseChange S := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul s x =>
    rcases x with ⟨c,q⟩
    simp [tensorPairEquiv,augment,TensorProduct.prodRight_tmul,LinearMap.baseChange_tmul,TensorProduct.tmul_add]

theorem augment_baseChange_surjective (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1)
    (ha : Function.Surjective (augment d f)) (S : Type u) [CommRing S] [Algebra R S] :
    Function.Surjective (augment (d.baseChange S) (f.baseChange S)) := by
  intro y
  obtain ⟨z,hz⟩ := (augment d f).baseChange_surjective S ha y
  refine ⟨tensorPairEquiv (R := R) (C0 := C0) (Q := Q) S z,?_⟩
  exact (LinearMap.congr_fun (augment_baseChange_comm d f S) z).trans hz

/-- The actual native kernel base-change map, followed by actual product
tensor identification. Flatness is required only of the ORIGINAL target. -/
def augmentedBoundaryBaseChangeEquiv [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) (ha : Function.Surjective (augment d f))
    (S : Type u) [CommRing S] [Algebra R S] :
    (S ⊗[R] LinearMap.ker (augment d f)) ≃ₗ[S]
      LinearMap.ker (augment (d.baseChange S) (f.baseChange S)) :=
  (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (augment d f) S)
    (FourCorner.MumfordKernel.kernel_baseChange_bijective (augment d f) ha S)).trans
      (kernelSourceEquiv _ _ (tensorPairEquiv S) (augment_baseChange_comm d f S))

theorem augmentedBoundaryBaseChangeEquiv_apply_val [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) (ha : Function.Surjective (augment d f))
    (S : Type u) [CommRing S] [Algebra R S] (z : S ⊗[R] LinearMap.ker (augment d f)) :
    (augmentedBoundaryBaseChangeEquiv d f ha S z).val =
      tensorPairEquiv S ((LinearMap.ker (augment d f)).subtype.baseChange S z) := by
  change tensorPairEquiv S (TwoChartCech.kerBaseChangeHom (augment d f) S z).val = _
  rw [TwoChartCech.kerBaseChangeHom_apply_coe]

theorem boundary_baseChange_comm [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) (ha : Function.Surjective (augment d f))
    (S : Type u) [CommRing S] [Algebra R S] :
    (boundary (d.baseChange S) (f.baseChange S)).comp
      (augmentedBoundaryBaseChangeEquiv d f ha S).toLinearMap = (boundary d f).baseChange S := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul s p =>
    change (augmentedBoundaryBaseChangeEquiv d f ha S (s ⊗ₜ[R] p)).val.2 = _
    rw [augmentedBoundaryBaseChangeEquiv_apply_val,LinearMap.baseChange_tmul]
    change (tensorPairEquiv S (s ⊗ₜ[R] p.val)).2 = s ⊗ₜ[R] (boundary d f p)
    rw [tensorPairEquiv,TensorProduct.prodRight_tmul]
    rfl

/-- Genuine H0 comparison for EVERY scalar algebra, including nonflat S. -/
def kernelBoundaryBaseChangeEquiv [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) (ha : Function.Surjective (augment d f))
    (S : Type u) [CommRing S] [Algebra R S] :
    LinearMap.ker ((boundary d f).baseChange S) ≃ₗ[S] LinearMap.ker (d.baseChange S) :=
  (kernelSourceEquiv _ _ (augmentedBoundaryBaseChangeEquiv d f ha S)
    (boundary_baseChange_comm d f ha S)).trans (kernelBoundaryEquiv (d.baseChange S) (f.baseChange S)).symm

/-- Genuine H1 comparison for EVERY scalar algebra, including nonflat S. -/
def cokerBoundaryBaseChangeEquiv [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) (ha : Function.Surjective (augment d f))
    (S : Type u) [CommRing S] [Algebra R S] :
    ((S ⊗[R] Q) ⧸ LinearMap.range ((boundary d f).baseChange S)) ≃ₗ[S]
      ((S ⊗[R] C1) ⧸ LinearMap.range (d.baseChange S)) := by
  have hr : LinearMap.range ((boundary d f).baseChange S) =
      LinearMap.range (boundary (d.baseChange S) (f.baseChange S)) := by
    rw [←boundary_baseChange_comm d f ha S]
    exact LinearMap.range_comp_of_range_eq_top _ (augmentedBoundaryBaseChangeEquiv d f ha S).range
  exact (Submodule.quotEquivOfEq _ _ hr).trans
    (cokerBoundaryEquiv (d.baseChange S) (f.baseChange S) (augment_baseChange_surjective d f ha S))
end FourCorner.EulerAugmentation
