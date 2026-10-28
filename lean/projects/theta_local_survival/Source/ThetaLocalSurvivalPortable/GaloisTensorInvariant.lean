import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Invariant.Defs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace FourCorner.ThetaLocalSurvival.ComponentDescent

variable (L A : Type) [Field L] [CommRing A] [Algebra ℚ L] [Algebra ℚ A]
abbrev tensorRing := L ⊗[ℚ] A

def tensorAut (σ : L ≃ₐ[ℚ] L) : tensorRing L A ≃ₐ[ℚ] tensorRing L A :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[ℚ] A)

@[simp] theorem tensorAut_tmul (σ : L ≃ₐ[ℚ] L) (l : L) (a : A) :
    tensorAut L A σ (l ⊗ₜ[ℚ] a)=σ l ⊗ₜ[ℚ] a := by
  change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id ℚ A) (l ⊗ₜ[ℚ] a)=_
  rw [Algebra.TensorProduct.map_tmul]
  rfl

def tensorActionHom : (L ≃ₐ[ℚ] L) →* (tensorRing L A ≃ₐ[ℚ] tensorRing L A) where
  toFun := tensorAut L A
  map_one' := by
    apply AlgEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a => simp
    | add x y hx hy => simp [map_add,hx,hy]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a => simp
    | add x y hx hy => simp [map_add,hx,hy]

instance (priority := 2000) tensorSMul : SMul (L ≃ₐ[ℚ] L) (tensorRing L A) :=
  ⟨fun σ x => tensorAut L A σ x⟩

instance tensorAction : MulSemiringAction (L ≃ₐ[ℚ] L) (tensorRing L A) :=
  MulSemiringAction.compHom (tensorRing L A) (tensorActionHom L A)

@[simp] theorem tensor_smul (σ : L ≃ₐ[ℚ] L) (x : tensorRing L A) :
    σ • x=tensorAut L A σ x := rfl

variable {L A} {ι : Type} (b : Module.Basis ι ℚ A)

theorem tensor_repr_galois (σ : L ≃ₐ[ℚ] L) (x : tensorRing L A) (i : ι) :
    (b.baseChange L).repr (σ • x) i=σ ((b.baseChange L).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp only [tensor_smul,tensorAut_tmul,Module.Basis.baseChange_repr_tmul]
    exact (map_smul σ (b.repr a i) l).symm
  | add x y hx hy => simp only [smul_add,map_add,Finsupp.add_apply,hx,hy]

/-- Actual fixed elements of the scalar-extended affine coordinate ring
descend coefficientwise to its original QQ-algebra. -/
theorem tensor_fixed_descends [IsGalois ℚ L] (x : tensorRing L A)
    (hx : ∀σ : L ≃ₐ[ℚ] L,σ • x=x) : ∃a : A,1 ⊗ₜ[ℚ] a=x := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ A
  let r := (b.baseChange L).repr
  have hfixed (i : Module.Basis.ofVectorSpaceIndex ℚ A) :
      ∀σ : L ≃ₐ[ℚ] L,σ (r x i)=r x i := by
    intro σ
    have h := congrArg (fun y : tensorRing L A => r y i) (hx σ)
    rw [tensor_repr_galois b] at h
    exact h
  have hcoeff (i : Module.Basis.ofVectorSpaceIndex ℚ A) :
      ∃q : ℚ,algebraMap ℚ L q=r x i :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (r x i)).mpr (hfixed i)
  let q := fun i => Classical.choose (hcoeff i)
  have hq (i) : algebraMap ℚ L (q i)=r x i := Classical.choose_spec (hcoeff i)
  let c : Module.Basis.ofVectorSpaceIndex ℚ A →₀ ℚ :=
    Finsupp.onFinset (r x).support q (by
      intro i hi
      by_contra hn
      apply hi
      apply (algebraMap ℚ L).injective
      rw [hq,Finsupp.notMem_support_iff.mp hn,map_zero])
  refine ⟨b.repr.symm c,?_⟩
  apply r.injective
  apply Finsupp.ext
  intro i
  change (b.baseChange L).repr (1 ⊗ₜ[ℚ] b.repr.symm c) i=r x i
  rw [Module.Basis.baseChange_repr_tmul,b.repr.apply_symm_apply]
  change q i • (1:L)=r x i
  rw [Algebra.smul_def,mul_one]
  exact hq i

end FourCorner.ThetaLocalSurvival.ComponentDescent
