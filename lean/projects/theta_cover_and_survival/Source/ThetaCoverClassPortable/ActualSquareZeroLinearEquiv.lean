import ThetaCoverClassPortable.ReplayImports
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Operations
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorProduct
universe u v w
namespace FourCorner.SquareZeroLifts
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (P : Type v) [AddCommGroup P] [Module R P]
def reduction : P →ₗ[R] (R ⧸ I) ⊗[R] P := TensorProduct.mk R (R ⧸ I) P 1
lemma reduction_surjective : Function.Surjective (reduction I P) := by
  unfold reduction
  rw [←TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ]
  exact (TensorProduct.quotTensorEquivQuotSMul P I).symm.surjective.comp (Submodule.mkQ_surjective _)
lemma reduction_eq_zero (x : P) : reduction I P x = 0 ↔ x ∈ I • (⊤ : Submodule R P) := by
  have h := congrArg (fun f : P →ₗ[R] P ⧸ (I • ⊤) => f x)
    (TensorProduct.quotTensorEquivQuotSMul_comp_mk (M:=P) I)
  change (1 : R ⧸ I) ⊗ₜ[R] x = 0 ↔ _
  rw [←(TensorProduct.quotTensorEquivQuotSMul P I).map_eq_zero_iff]
  rw [show (TensorProduct.quotTensorEquivQuotSMul P I) (1 ⊗ₜ[R] x) = Submodule.Quotient.mk x from h]
  exact Submodule.Quotient.mk_eq_zero _
lemma end_square_zero (hI : I^2=⊥) (f : P →ₗ[R] P)
    (hf : ∀x,f x∈I • (⊤ : Submodule R P)) : ∀x,f (f x)=0 := by
  have hr : LinearMap.range f ≤ I • (⊤ : Submodule R P) := by
    rintro _ ⟨x,rfl⟩;exact hf x
  have hm : (I • (⊤ : Submodule R P)).map f ≤ ⊥ := by
    rw [Submodule.map_smul'',Submodule.map_top]
    calc I • LinearMap.range f ≤ I • (I • (⊤ : Submodule R P)) := smul_le_smul_left I hr
      _ = ⊥ := by rw [←mul_smul,←pow_two,hI];simp
  intro x
  exact hm (Submodule.mem_map_of_mem (hf x))

variable {P} {Q : Type w} [AddCommGroup Q] [Module R Q]
/-- Lifts an actual prescribed quotient isomorphism, compatibly on every element. -/
theorem compatible_equiv (hI:I^2=⊥) [Module.Projective R P] [Module.Projective R Q]
    (e : (R⧸I)⊗[R]P ≃ₗ[R⧸I] (R⧸I)⊗[R]Q) :
    ∃ f : P ≃ₗ[R] Q,∀x,(1:R⧸I)⊗ₜ[R]f x=e ((1:R⧸I)⊗ₜ[R]x) := by
  obtain ⟨f,hf⟩ := Module.projective_lifting_property (reduction I Q)
    ((e.restrictScalars R).toLinearMap.comp (reduction I P)) (reduction_surjective I Q)
  obtain ⟨g,hg⟩ := Module.projective_lifting_property (reduction I P)
    ((e.symm.restrictScalars R).toLinearMap.comp (reduction I Q)) (reduction_surjective I P)
  have hf' (x:P) : reduction I Q (f x)=e (reduction I P x) := congrArg (fun h:P→ₗ[R]_=>h x) hf
  have hg' (y:Q) : reduction I P (g y)=e.symm (reduction I Q y) := congrArg (fun h:Q→ₗ[R]_=>h y) hg
  let a : P→ₗ[R]P := g.comp f-LinearMap.id
  let b : Q→ₗ[R]Q := f.comp g-LinearMap.id
  have ha : ∀x,a x∈I • (⊤ : Submodule R P) := by
    intro x;apply (reduction_eq_zero I P _).mp
    change reduction I P (g (f x)-x)=0
    rw [map_sub,hg',hf',e.symm_apply_apply,sub_self]
  have hb : ∀y,b y∈I • (⊤ : Submodule R Q) := by
    intro y;apply (reduction_eq_zero I Q _).mp
    change reduction I Q (f (g y)-y)=0
    rw [map_sub,hf',hg',e.apply_symm_apply,sub_self]
  have haa := end_square_zero I P hI a ha
  have hbb := end_square_zero I Q hI b hb
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    have heq : a x = -x := by simp [a,hx]
    have : -a x=0 := by simpa only [heq,map_neg] using haa x
    rw [heq,neg_neg] at this
    exact this
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨g (y-b y),?_⟩
    have hh := hbb y
    change f (g (f (g y)-y))-(f (g y)-y)=0 at hh
    simp only [map_sub] at hh ⊢
    change f (g y)-f (g (f (g y)-y))=y
    simp only [map_sub]
    exact sub_eq_iff_eq_add.mpr (by rw [sub_eq_zero] at hh; rw [hh]; abel)
  exact ⟨LinearEquiv.ofBijective f ⟨hinj,hsurj⟩,hf'⟩
end FourCorner.SquareZeroLifts

namespace Module.Projective
variable {R : Type u} [CommRing R]
theorem exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
    (I:Ideal R)(hI:I^2=⊥)(P:Type v)(Q:Type w)
    [AddCommGroup P][Module R P][AddCommGroup Q][Module R Q]
    [Module.Projective R P][Module.Projective R Q]
    (e:(R⧸I)⊗[R]P ≃ₗ[R⧸I] (R⧸I)⊗[R]Q) :
    ∃f:P≃ₗ[R]Q,∀x,(1:R⧸I)⊗ₜ[R]f x=e ((1:R⧸I)⊗ₜ[R]x) :=
  FourCorner.SquareZeroLifts.compatible_equiv I hI e

theorem nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
    (I:Ideal R)(hI:I^2=⊥)(P:Type v)(Q:Type w)
    [AddCommGroup P][Module R P][AddCommGroup Q][Module R Q]
    [Module.Projective R P][Module.Projective R Q]
    (e:(R⧸I)⊗[R]P ≃ₗ[R⧸I] (R⧸I)⊗[R]Q) : Nonempty (P≃ₗ[R]Q) := by
  obtain ⟨f,_⟩ := exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat I hI P Q e
  exact ⟨f⟩
#print axioms exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
end Module.Projective
