import ThetaCoverClassPortable.FlatTensorKernel
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
namespace FourCorner.IdealFlatDescent
open Algebra.TensorProduct
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- A genuine ideal satisfying the two tensor-extension descent conditions
is the extension of its actual contraction. Flatness alone suffices. -/
theorem map_comap_of_tensor_invariance (I : Ideal S)
    (hI : I.map (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S) =
      I.map (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom) :
    (I.comap (algebraMap R S)).map (algebraMap R S)=I := by
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  let q : S →ₐ[R] S ⧸ I := Ideal.Quotient.mkₐ R I
  let g : R →ₐ[R] S ⧸ I := q.comp (Algebra.ofId R S)
  let F := Algebra.TensorProduct.map (AlgHom.id R S) g
  let G := Algebra.TensorProduct.map (AlgHom.id R S) q
  have hg : RingHom.ker g.toRingHom=I.comap (algebraMap R S) := by
    ext r
    change Ideal.Quotient.mk I (algebraMap R S r)=0 ↔ algebraMap R S r ∈ I
    exact Ideal.Quotient.eq_zero_iff_mem
  have hG : RingHom.ker G.toRingHom=
      I.map (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S).toRingHom := by
    change RingHom.ker G = I.map
      (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)
    have hq : RingHom.ker q = I := by
      ext z
      change Ideal.Quotient.mk I z=0 ↔ z ∈ I
      exact Ideal.Quotient.eq_zero_iff_mem
    have hh := Algebra.TensorProduct.lTensor_ker (A:=S) q (Ideal.Quotient.mkₐ_surjective R I)
    rw [hq] at hh
    exact hh
  have hzG : G (x ⊗ₜ[R] (1:S))=0 := by
    change x ⊗ₜ[R] (1:S) ∈ RingHom.ker G.toRingHom
    rw [hG,←hI]
    exact Ideal.mem_map_of_mem _ hx
  have hzF : F (x ⊗ₜ[R] (1:R))=0 := by
    simpa only [F,G,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,map_one] using hzG
  have hF : RingHom.ker F.toRingHom=
      (I.comap (algebraMap R S)).map
        (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom := by
    simpa only [F,hg] using (tensor_kernel_of_flat (A:=S) g)
  have hxF : x ⊗ₜ[R] (1:R) ∈ (I.comap (algebraMap R S)).map
      (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom := by
    rw [←hF]
    exact hzF
  let e := Algebra.TensorProduct.rid R R S
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : R →ₐ[R] S ⊗[R] R).toRingHom = algebraMap R S := by
    ext r
    simp [e,Algebra.smul_def]
  have hm := Ideal.mem_map_of_mem e.toRingHom hxF
  rw [Ideal.map_map,he] at hm
  change (Algebra.TensorProduct.rid R R S) (x ⊗ₜ[R] (1:R)) ∈
    (I.comap (algebraMap R S)).map (algebraMap R S) at hm
  simpa only [Algebra.TensorProduct.rid_tmul,one_smul] using hm

end FourCorner.IdealFlatDescent
#print axioms FourCorner.IdealFlatDescent.map_comap_of_tensor_invariance
