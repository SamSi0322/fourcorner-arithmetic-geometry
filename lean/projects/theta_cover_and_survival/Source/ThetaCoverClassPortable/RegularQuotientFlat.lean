import ThetaCoverClassPortable.IdealTensor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

noncomputable section
set_option autoImplicit false
open scoped TensorProduct nonZeroDivisors
universe u v w
namespace FourCorner.RegularQuotientFlat
open IdealTensor
variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- Naturality of the actual multiplication map under an actual algebra map. -/
theorem idealTensorMap_naturality {C : Type w} [CommRing C] [Algebra A C]
    (f : B →ₐ[A] C) (I : Ideal A) (z : B ⊗[A] I) :
    idealTensorMap I ((f.toLinearMap.rTensor I) z) = f (idealTensorMap I z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b a =>
    rw [LinearMap.rTensor_tmul,idealTensorMap_tmul,idealTensorMap_tmul,map_mul,f.commutes]
    rfl
  | add x y hx hy => simp only [map_add,hx,hy]

/-- The actual quotient/tensor map kills multiplication by the defining g. -/
theorem quotientTensor_smul_eq_zero (g : B) (I : Ideal A) (z : B ⊗[A] I) :
    (((Ideal.Quotient.mkₐ A (Ideal.span {g})).toLinearMap.rTensor I) (g • z)) = 0 := by
  let q := Ideal.Quotient.mkₐ A (Ideal.span {g})
  have hg : q g=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g)
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero,map_zero]
  | tmul b a =>
    rw [TensorProduct.smul_tmul',smul_eq_mul,LinearMap.rTensor_tmul]
    change q (g*b) ⊗ₜ[A] a = 0
    rw [map_mul,hg,zero_mul,TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add,map_add,hx,hy,add_zero]

/-- Flatness of the original algebra and regularity modulo EVERY extended
base ideal prove injectivity of the actual ideal multiplication map in B/(g).
No finite/free/projective/Noetherian or desired quotient-flatness premise. -/
theorem quotient_idealTensorMap_injective [Module.Flat A B] (g : B)
    (hreg : ∀ (I : Ideal A) (b : B),
      g*b ∈ Ideal.map (algebraMap A B) I → b ∈ Ideal.map (algebraMap A B) I)
    (I : Ideal A) :
    Function.Injective (idealTensorMap (S := B ⧸ Ideal.span {g}) I) := by
  let Q := B ⧸ Ideal.span {g}
  let q : B →ₐ[A] Q := Ideal.Quotient.mkₐ A (Ideal.span {g})
  let t : B ⊗[A] I →ₗ[A] Q ⊗[A] I := q.toLinearMap.rTensor I
  have ht : Function.Surjective t := LinearMap.rTensor_surjective I (Ideal.Quotient.mkₐ_surjective A _)
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨y,rfl⟩ := ht z
  have hq : q (idealTensorMap I y)=0 := by
    rw [←idealTensorMap_naturality q I y]
    exact hz
  have hyJ : idealTensorMap I y ∈ Ideal.span {g} := Ideal.Quotient.eq_zero_iff_mem.mp hq
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hyJ
  have hyI : idealTensorMap I y ∈ Ideal.map (algebraMap A B) I :=
    idealTensorMap_range (S := B) I ▸ LinearMap.mem_range_self _ y
  have hbI : b ∈ Ideal.map (algebraMap A B) I := hreg I b (hb ▸ hyI)
  have hbR : b ∈ LinearMap.range (idealTensorMap (S := B) I) :=
    (idealTensorMap_range (S := B) I).symm ▸ hbI
  obtain ⟨w,hw⟩ := hbR
  have hyw : y=g • w := idealTensorMap_injective (S := B) I (by
    rw [map_smul,hw,smul_eq_mul]
    exact hb)
  rw [hyw]
  exact quotientTensor_smul_eq_zero g I w

/-- The native all-ideal tensor criterion proves genuine quotient flatness. -/
theorem quotient_flat_of_allIdeal_regular [Module.Flat A B] (g : B)
    (hreg : ∀ (I : Ideal A) (b : B),
      g*b ∈ Ideal.map (algebraMap A B) I → b ∈ Ideal.map (algebraMap A B) I) :
    Module.Flat A (B ⧸ Ideal.span {g}) := by
  apply (Module.Flat.iff_lTensor_injective').mpr
  intro I x y hxy
  apply quotient_idealTensorMap_injective g hreg I
  have h : (I.subtype.baseChange (B ⧸ Ideal.span {g})) x =
      (I.subtype.baseChange (B ⧸ Ideal.span {g})) y := by
    simpa only [LinearMap.baseChange_eq_ltensor] using hxy
  exact congrArg (Algebra.TensorProduct.rid A (B ⧸ Ideal.span {g}) (B ⧸ Ideal.span {g})) h

/-- The precise algebraic half of the regular-fibre quotient-flatness argument:
only actual original flatness and actual regularity modulo all extended ideals
are hypotheses. Noetherian induction producing that hypothesis is separate. -/
theorem regular_and_quotient_flat_of_allIdeal_regular [Module.Flat A B] (g : B)
    (hreg : ∀ (I : Ideal A) (b : B),
      g*b ∈ Ideal.map (algebraMap A B) I → b ∈ Ideal.map (algebraMap A B) I) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) := by
  have hg : ∀ b : B, g*b=0 → b=0 := by
    intro b hb
    have h : g*b ∈ Ideal.map (algebraMap A B) (⊥ : Ideal A) := by simpa [hb]
    have := hreg ⊥ b h
    simpa only [Ideal.map_bot,Ideal.mem_bot] using this
  exact ⟨mem_nonZeroDivisors_iff.mpr ⟨hg,fun b hb => hg b (by rwa [mul_comm])⟩,
    quotient_flat_of_allIdeal_regular g hreg⟩

/-- Equivalent native quotient/nonZeroDivisors spelling of the same interface. -/
theorem regular_and_quotient_flat_of_regular_all_quotients [Module.Flat A B] (g : B)
    (hreg : ∀ I : Ideal A, Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) g ∈
      nonZeroDivisors (B ⧸ Ideal.map (algebraMap A B) I)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) := by
  apply regular_and_quotient_flat_of_allIdeal_regular g
  intro I b hb
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (mem_nonZeroDivisors_iff.mp (hreg I)).1
  rw [←map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
end FourCorner.RegularQuotientFlat
