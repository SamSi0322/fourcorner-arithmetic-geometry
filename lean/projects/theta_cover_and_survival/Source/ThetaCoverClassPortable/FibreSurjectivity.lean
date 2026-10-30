import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support

namespace FourCorner.MumfordKernel
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R]
variable {C0 C1 : Type v} [AddCommGroup C0] [AddCommGroup C1] [Module R C0] [Module R C1]

/-- The ACTUAL scalar tensor of the actual cokernel is zero whenever the
base-changed differential is surjective. No quotient/model isomorphism is
assumed: surjectivity of the true tensor quotient and its zero composite
prove this directly. -/
theorem tensor_coker_subsingleton (d : C0 →ₗ[R] C1) (S : Type w) [CommRing S] [Algebra R S]
    (hdS : Function.Surjective (d.baseChange S)) :
    Subsingleton (S ⊗[R] (C1 ⧸ LinearMap.range d)) := by
  let q := (LinearMap.range d).mkQ
  have hq : Function.Surjective (q.baseChange S) := q.lTensor_surjective S (LinearMap.range d).mkQ_surjective
  have hcomp : q.comp d=0 := by
    apply LinearMap.ext
    intro x
    change (LinearMap.range d).mkQ (d x)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩
  have hcompS : (q.baseChange S).comp (d.baseChange S)=0 := by
    rw [← LinearMap.baseChange_comp,hcomp,LinearMap.baseChange_zero]
  apply (subsingleton_iff_forall_eq 0).mpr
  intro z
  obtain ⟨y,hy⟩ := hq z
  obtain ⟨x,hx⟩ := hdS y
  have h := LinearMap.congr_fun hcompS x
  change q.baseChange S (d.baseChange S x)=0 at h
  rw [hx,hy] at h
  exact h

/-- Finite cokernel + surjectivity on EVERY field fibre genuinely force
the ORIGINAL d surjective, by exact support/residue detection. No finite
C0/C1, no flat C0/C1, and no original-surjectivity premise is introduced. -/
theorem surjective_of_field_fibres (d : C0 →ₗ[R] C1)
    [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],Function.Surjective (d.baseChange K)) :
    Function.Surjective d := by
  let Q := C1 ⧸ LinearMap.range d
  have hsub (p : PrimeSpectrum R) : Subsingleton (p.asIdeal.ResidueField ⊗[R] Q) :=
    tensor_coker_subsingleton d p.asIdeal.ResidueField (hfib _)
  have hsupp : Module.support R Q=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hnon : Nontrivial (p.asIdeal.ResidueField ⊗[R] Q) :=
      (Module.mem_support_iff_nontrivial_residueField_tensorProduct (R:=R) (M:=Q) p).mp hp
    exact (not_nontrivial_iff_subsingleton.mpr (hsub p)) hnon
  have hQ : Subsingleton Q := (Module.support_eq_empty_iff (R:=R) (M:=Q)).mp hsupp
  have hrange : LinearMap.range d=⊤ := by
    simpa only [Q,Submodule.Quotient.subsingleton_iff] using hQ
  exact LinearMap.range_eq_top.mp hrange

#print axioms tensor_coker_subsingleton
#print axioms surjective_of_field_fibres
end
end FourCorner.MumfordKernel
