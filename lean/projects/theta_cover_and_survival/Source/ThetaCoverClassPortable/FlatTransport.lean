import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

namespace FourCorner.FlatTransport
noncomputable section
open scoped TensorProduct
universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The multiplication map on the tensor product with the actual ideal. -/
def idealMultiply (I : Ideal A) : B ⊗[A] I →ₗ[A] B :=
  (Algebra.TensorProduct.rid A B B).toLinearMap.restrictScalars A |>.comp (I.subtype.lTensor B)

@[simp] theorem idealMultiply_tmul (I : Ideal A) (b : B) (a : I) :
    idealMultiply I (b ⊗ₜ[A] a) = algebraMap A B (a : A) * b := by
  simp [idealMultiply, Algebra.smul_def]

theorem mem_range_idealMultiply (I : Ideal A) (x : B) :
    x ∈ LinearMap.range (idealMultiply (B:=B) I) ↔ x ∈ I.map (algebraMap A B) := by
  constructor
  · rintro ⟨z,rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      rw [idealMultiply_tmul]
      exact (I.map _).mul_mem_right b (Ideal.mem_map_of_mem _ a.property)
    | add z z' hz hz' => simpa only [map_add] using (I.map _).add_mem hz hz'
  · have hle : I.map (algebraMap A B) ≤
        (LinearMap.range ((Algebra.TensorProduct.rid A B B).toLinearMap.comp
          (I.subtype.baseChange B)) : Submodule B B) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      exact ⟨1 ⊗ₜ[A] (⟨a,ha⟩ : I), by simp [Algebra.smul_def]⟩
    intro hx
    obtain ⟨z,hz⟩ := hle hx
    exact ⟨z,hz⟩

/-- Flat tensoring transports the actual kernel of a map out of the base ring. -/
theorem tensor_unit_eq_zero_iff_mem_map_ker [Module.Flat A B]
    {M : Type w} [AddCommGroup M] [Module A M] (f : A →ₗ[A] M) (x : B) :
    f.lTensor B (x ⊗ₜ[A] (1 : A)) = 0 ↔
      x ∈ Ideal.map (algebraMap A B) (LinearMap.ker f) := by
  have he := Module.Flat.lTensor_exact B f.exact_subtype_ker_map
  rw [← mem_range_idealMultiply]
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := (he (x ⊗ₜ[A] (1 : A))).mp hx
    refine ⟨z, ?_⟩
    change (Algebra.TensorProduct.rid A B B) ((LinearMap.ker f).subtype.lTensor B z) = x
    rw [hz]
    simp
  · rintro ⟨z,hz⟩
    apply (he (x ⊗ₜ[A] (1 : A))).mpr
    refine ⟨z, ?_⟩
    apply (Algebra.TensorProduct.rid A B B).injective
    change idealMultiply (LinearMap.ker f) z = _
    simpa only [Algebra.TensorProduct.rid_tmul, one_smul] using hz

/-- Scalar multiplication followed by quotienting, on the base ring. -/
def mulQuotient (I : Ideal A) (a : A) : A →ₗ[A] A ⧸ I :=
  I.mkQ.comp (LinearMap.mulLeft A a)

@[simp] theorem ker_mulQuotient (I : Ideal A) (a : A) :
    LinearMap.ker (mulQuotient I a) = I.colon ({a} : Set A) := by
  ext r
  change Ideal.Quotient.mk I (a*r) = 0 ↔ r ∈ I.colon ({a} : Set A)
  rw [Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_colon_singleton]
  simp [mul_comm]

 theorem mem_map_colon_singleton_iff [Module.Flat A B] (I : Ideal A) (a : A) (x : B) :
    x ∈ (I.colon ({a} : Set A)).map (algebraMap A B) ↔
      algebraMap A B a * x ∈ I.map (algebraMap A B) := by
  rw [← ker_mulQuotient]
  rw [← tensor_unit_eq_zero_iff_mem_map_ker]
  have hI : LinearMap.ker I.mkQ = I := Submodule.ker_mkQ I
  have hq := tensor_unit_eq_zero_iff_mem_map_ker (B:=B) I.mkQ (algebraMap A B a * x)
  simp only [hI] at hq
  rw [← hq]
  have ht : (mulQuotient I a).lTensor B (x ⊗ₜ[A] (1 : A)) =
      I.mkQ.lTensor B ((algebraMap A B a * x) ⊗ₜ[A] (1 : A)) := by
    simp only [LinearMap.lTensor_tmul, mulQuotient, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, mul_one]
    rw [← Algebra.smul_def,
      TensorProduct.smul_tmul]
    congr 1
    rw [← map_smul]
    simp
  rw [ht]

 theorem map_colon_singleton [Module.Flat A B] (I : Ideal A) (a : A) :
    (I.colon ({a} : Set A)).map (algebraMap A B) =
      (I.map (algebraMap A B)).colon ({algebraMap A B a} : Set B) := by
  ext x
  rw [mem_map_colon_singleton_iff, Submodule.mem_colon_singleton]
  simp [mul_comm]

 theorem mem_map_colon_singleton_of_mul_mem [Module.Flat A B]
    (I : Ideal A) (a : A) (x : B) (h : algebraMap A B a * x ∈ I.map (algebraMap A B)) :
    x ∈ (I.colon ({a} : Set A)).map (algebraMap A B) :=
  (mem_map_colon_singleton_iff I a x).mpr h

 theorem ker_includeLeft_residueField [Module.Flat A B] (p : Ideal A) [p.IsPrime] :
    RingHom.ker (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] p.ResidueField).toRingHom =
      p.map (algebraMap A B) := by
  ext x
  have hp : (LinearMap.ker (Algebra.linearMap A p.ResidueField) : Ideal A) = p :=
    p.ker_algebraMap_residueField
  simpa [hp, LinearMap.lTensor_tmul] using
    (tensor_unit_eq_zero_iff_mem_map_ker (B:=B) (Algebra.linearMap A p.ResidueField) x)

end
end FourCorner.FlatTransport
