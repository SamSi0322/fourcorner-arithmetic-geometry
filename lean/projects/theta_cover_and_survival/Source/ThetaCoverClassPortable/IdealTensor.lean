import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Tensor

namespace FourCorner.RegularQuotientFlat.IdealTensor
noncomputable section
open scoped TensorProduct
universe u v
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

/-- Genuine multiplication map S tensor_R I→S on the ACTUAL ideal I. -/
def idealTensorMap (I : Ideal R) : S ⊗[R] I →ₗ[S] S :=
  (Algebra.TensorProduct.rid R S S).toLinearMap.comp (I.subtype.baseChange S)

 theorem idealTensorMap_tmul (I : Ideal R) (s : S) (a : I) :
    idealTensorMap I (s ⊗ₜ[R] a)=algebraMap R S (a : R)*s := by
  simp [idealTensorMap,Algebra.smul_def]

 theorem idealTensorMap_range (I : Ideal R) :
    LinearMap.range (idealTensorMap (S:=S) I)=Ideal.map (algebraMap R S) I := by
  have hm (z : S ⊗[R] I) : idealTensorMap I z∈Ideal.map (algebraMap R S) I := by
    induction z using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (Ideal.map (algebraMap R S) I).zero_mem
    | tmul s a =>
        rw [idealTensorMap_tmul]
        exact (Ideal.map (algebraMap R S) I).mul_mem_right s (Ideal.mem_map_of_mem _ a.property)
    | add x y hx hy => rw [map_add];exact (Ideal.map (algebraMap R S) I).add_mem hx hy
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    exact hm z
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact ⟨1 ⊗ₜ[R] (⟨a,ha⟩ : I),by rw [idealTensorMap_tmul,mul_one]⟩

 theorem idealTensorMap_injective [Module.Flat R S] (I : Ideal R) :
    Function.Injective (idealTensorMap (S:=S) I) := by
  have hi : Function.Injective (I.subtype.baseChange S) :=
    Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.subtype_injective
  exact (Algebra.TensorProduct.rid R S S).injective.comp hi

/-- Actual ideal base change is an isomorphism onto the ACTUAL extended
ideal, from genuine flatness, with no module-descent certificate assumed. -/
def idealTensorEquiv [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] I ≃ₗ[S] Ideal.map (algebraMap R S) I := by
  let f := idealTensorMap (S:=S) I
  have hf (z) : f z∈Ideal.map (algebraMap R S) I :=
    idealTensorMap_range (S:=S) I ▸ LinearMap.mem_range_self f z
  apply LinearEquiv.ofBijective (f.codRestrict _ hf)
  constructor
  · intro x y hxy
    exact idealTensorMap_injective (S:=S) I (congrArg Subtype.val hxy)
  · intro a
    have ha : (a : S)∈LinearMap.range f := (idealTensorMap_range (S:=S) I).symm ▸ a.property
    obtain ⟨z,hz⟩ := ha
    exact ⟨z,Subtype.ext hz⟩

#print axioms idealTensorMap_range
#print axioms idealTensorMap_injective
#print axioms idealTensorEquiv
end
end FourCorner.RegularQuotientFlat.IdealTensor
