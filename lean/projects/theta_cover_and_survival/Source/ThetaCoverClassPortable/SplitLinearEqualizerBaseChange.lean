import ThetaCoverClassPortable.ProjectiveTraceBaseChange

namespace FourCorner.SplitLinearEqualizerBaseChange
noncomputable section
open scoped TensorProduct
universe u v w z
variable {R : Type u} [CommRing R]
variable {L : Type v} [AddCommGroup L] [Module R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type z} [AddCommGroup N] [Module R N]

/-- A PROVED explicit contracting homotopy, rather than flatness of the
base change, suffices for exactness after every scalar change. This lemma
is applied below to the actual invariant trace maps. -/
theorem range_eq_ker (i : L →ₗ[R] M) (d : M →ₗ[R] N)
    (r : M →ₗ[R] L) (h : N →ₗ[R] M)
    (hdi : d.comp i=0) (hhd : h.comp d=LinearMap.id-i.comp r) :
    LinearMap.range i=LinearMap.ker d := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change d (i y)=0
    exact LinearMap.congr_fun hdi y
  · intro hx
    refine ⟨r x,?_⟩
    have hh := LinearMap.congr_fun hhd x
    change h (d x)=x-i (r x) at hh
    rw [LinearMap.mem_ker.mp hx,map_zero] at hh
    exact (sub_eq_zero.mp hh.symm).symm

 theorem baseChange_range_eq_ker (i : L →ₗ[R] M) (d : M →ₗ[R] N)
    (r : M →ₗ[R] L) (h : N →ₗ[R] M)
    (hdi : d.comp i=0) (hhd : h.comp d=LinearMap.id-i.comp r)
    (S : Type*) [CommRing S] [Algebra R S] :
    LinearMap.range (i.baseChange S)=LinearMap.ker (d.baseChange S) := by
  apply range_eq_ker (i.baseChange S) (d.baseChange S) (r.baseChange S) (h.baseChange S)
  · have hh := congrArg (fun f=>f.baseChange S) hdi
    simpa only [LinearMap.baseChange_comp,LinearMap.baseChange_zero] using hh
  · have hh := congrArg (fun f=>f.baseChange S) hhd
    simpa only [LinearMap.baseChange_comp,LinearMap.baseChange_sub,LinearMap.baseChange_id] using hh

 theorem baseChange_retraction (i : L →ₗ[R] M) (r : M →ₗ[R] L)
    (hri : r.comp i=LinearMap.id) (S : Type*) [CommRing S] [Algebra R S] :
    (r.baseChange S).comp (i.baseChange S)=LinearMap.id := by
  have hh := congrArg (fun f=>f.baseChange S) hri
  simpa only [LinearMap.baseChange_comp,LinearMap.baseChange_id] using hh

#print axioms baseChange_range_eq_ker
#print axioms baseChange_retraction
end
end FourCorner.SplitLinearEqualizerBaseChange
