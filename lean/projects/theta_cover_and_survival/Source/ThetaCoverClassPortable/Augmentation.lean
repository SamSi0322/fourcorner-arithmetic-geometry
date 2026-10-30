import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact.Basic

noncomputable section
set_option autoImplicit false
universe u
namespace FourCorner.EulerAugmentation
variable {R C0 C1 Q : Type u} [CommRing R]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup Q] [Module R Q]

def augment (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) : (C0 × Q) →ₗ[R] C1 := d.coprod f

def boundary (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) : LinearMap.ker (augment d f) →ₗ[R] Q :=
  (LinearMap.snd R C0 Q).comp (LinearMap.ker (augment d f)).subtype

def kernelToAug (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) :
    LinearMap.ker d →ₗ[R] LinearMap.ker (augment d f) where
  toFun x := ⟨(x.val,0),by change d x.val+f 0=0;rw [x.property,map_zero,add_zero]⟩
  map_add' x y := by apply Subtype.ext;ext <;>simp
  map_smul' r x := by apply Subtype.ext;ext <;>simp

/-- Actual cycles of P->Q are literally the original kernel via x |-> (x,0). -/
def kernelBoundaryEquiv (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) :
    LinearMap.ker d ≃ₗ[R] LinearMap.ker (boundary d f) := by
  let a := (kernelToAug d f).codRestrict (LinearMap.ker (boundary d f)) (fun x => show boundary d f (kernelToAug d f x)=0 from rfl)
  apply LinearEquiv.ofBijective a
  constructor
  · intro x y h
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker (boundary d f) => z.val.val.1) h
  · intro z
    have hq : z.val.val.2=0 := z.property
    have hd : d z.val.val.1=0 := by
      have h := z.val.property
      change d z.val.val.1+f z.val.val.2=0 at h
      rwa [hq,map_zero,add_zero] at h
    refine ⟨⟨z.val.val.1,hd⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl hq.symm

def cokerMap (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) : Q →ₗ[R] C1 ⧸ LinearMap.range d :=
  (LinearMap.range d).mkQ.comp f

theorem boundary_exact (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1) :
    Function.Exact (boundary d f) (cokerMap d f) := by
  intro q
  constructor
  · intro h
    have hm : f q ∈ LinearMap.range d := (Submodule.Quotient.mk_eq_zero _).mp h
    obtain ⟨c,hc⟩ := hm
    refine ⟨⟨(-c,q),?_⟩,rfl⟩
    change d (-c)+f q=0
    rw [map_neg,hc,neg_add_cancel]
  · rintro ⟨p,rfl⟩
    change (LinearMap.range d).mkQ (f p.val.2)=0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨-p.val.1,?_⟩
    rw [map_neg]
    apply Eq.symm
    apply eq_neg_iff_add_eq_zero.mpr
    have h := p.property
    change d p.val.1+f p.val.2=0 at h
    simpa only [add_comm] using h

theorem cokerMap_surjective (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1)
    (ha : Function.Surjective (augment d f)) : Function.Surjective (cokerMap d f) := by
  intro z
  obtain ⟨y,rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨c,q⟩,h⟩ := ha y
  change d c+f q=y at h
  have h0 : (LinearMap.range d).mkQ (d c)=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)
  refine ⟨q,?_⟩
  have hh := congrArg (LinearMap.range d).mkQ h
  rw [map_add,h0,zero_add] at hh
  exact hh

/-- Genuine cokernel comparison induced by f; no comparison is supplied as a premise. -/
def cokerBoundaryEquiv (d : C0 →ₗ[R] C1) (f : Q →ₗ[R] C1)
    (ha : Function.Surjective (augment d f)) :
    (Q ⧸ LinearMap.range (boundary d f)) ≃ₗ[R] (C1 ⧸ LinearMap.range d) :=
  (boundary_exact d f).linearEquivOfSurjective (cokerMap_surjective d f ha)
end FourCorner.EulerAugmentation
