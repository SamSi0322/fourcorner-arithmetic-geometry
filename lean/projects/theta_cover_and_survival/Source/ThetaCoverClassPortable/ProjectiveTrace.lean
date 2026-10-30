import ThetaCoverClassPortable.ProjectiveNormBaseChange
import Mathlib.LinearAlgebra.Trace

/-! Genuine finite-projective trace. Every use of native trace is ONLY
on an explicitly finite free ambient R^m. The original module stays
finite projective and can have nonconstant rank. -/
namespace FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

 def ambientOperator (p : Frame R M) : Module.End R M →ₗ[R] Module.End R (Fin p.size → R) where
  toFun f := p.sectionMap.comp (f.comp p.projection)
  map_add' f g := by simp only [LinearMap.add_comp,LinearMap.comp_add]
  map_smul' r f := by simp only [LinearMap.smul_comp,LinearMap.comp_smul,RingHom.id_apply]

 def traceAlong (p : Frame R M) : Module.End R M →ₗ[R] R :=
  (LinearMap.trace R (Fin p.size → R)).comp (ambientOperator p)

 theorem traceAlong_independent (p q : Frame R M) (f : Module.End R M) :
    traceAlong p f=traceAlong q f := by
  let U := p.sectionMap.comp (f.comp q.projection)
  let V := q.sectionMap.comp p.projection
  have hUV : U.comp V=p.sectionMap.comp (f.comp p.projection) := by
    apply LinearMap.ext
    intro x
    simp only [U,V,LinearMap.comp_apply,split_apply]
  have hVU : V.comp U=q.sectionMap.comp (f.comp q.projection) := by
    apply LinearMap.ext
    intro x
    simp only [U,V,LinearMap.comp_apply,split_apply]
  change LinearMap.trace R _ (p.sectionMap.comp (f.comp p.projection))=
    LinearMap.trace R _ (q.sectionMap.comp (f.comp q.projection))
  rw [← hUV,← hVU]
  exact LinearMap.trace_comp_comm' V U

/-- The trace of any finite-projective endomorphism, proved independent
of the actual finite free retraction chosen to define it. -/
def projectiveTrace [Module.Finite R M] [Module.Projective R M] : Module.End R M →ₗ[R] R :=
  traceAlong (ofFiniteProjective R M)

 theorem traceAlong_intertwiner (p : Frame R M) (q : Frame R N)
    (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N)
    (he : e.toLinearMap.comp f=g.comp e.toLinearMap) :
    traceAlong p f=traceAlong q g := by
  let U := p.sectionMap.comp (e.symm.toLinearMap.comp q.projection)
  let V := q.sectionMap.comp (e.toLinearMap.comp (f.comp p.projection))
  have hUV : U.comp V=p.sectionMap.comp (f.comp p.projection) := by
    apply LinearMap.ext
    intro x
    simp only [U,V,LinearMap.comp_apply,LinearEquiv.coe_coe,split_apply,LinearEquiv.symm_apply_apply]
  have hVU : V.comp U=q.sectionMap.comp (g.comp q.projection) := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun he (e.symm (q.projection x))
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] at hx
    simp only [U,V,LinearMap.comp_apply,LinearEquiv.coe_coe,split_apply,hx]
  change LinearMap.trace R _ (p.sectionMap.comp (f.comp p.projection))=
    LinearMap.trace R _ (q.sectionMap.comp (g.comp q.projection))
  rw [← hUV,← hVU]
  exact LinearMap.trace_comp_comm' V U

 theorem traceAlong_transport (p : Frame R M) (e : M ≃ₗ[R] N)
    (f : Module.End R M) (g : Module.End R N)
    (he : e.toLinearMap.comp f=g.comp e.toLinearMap) :
    traceAlong (transportFrame p e) g=traceAlong p f :=
  (traceAlong_intertwiner p (transportFrame p e) e f g he).symm

/-- Agreement with the standard trace is asserted only if the ORIGINAL
module actually IS finite free, never inferred from projectivity. -/
theorem traceAlong_eq_free [Module.Free R M] [Module.Finite R M]
    (p : Frame R M) (f : Module.End R M) :
    traceAlong p f=LinearMap.trace R M f := by
  change LinearMap.trace R _ (p.sectionMap.comp (f.comp p.projection))=_
  have hc := (LinearMap.trace_comp_comm' p.sectionMap (f.comp p.projection)).symm
  have h : (f.comp p.projection).comp p.sectionMap=f := by
    rw [LinearMap.comp_assoc,p.split,LinearMap.comp_id]
  rw [h] at hc
  exact hc

#print axioms traceAlong_independent
#print axioms traceAlong_intertwiner
#print axioms traceAlong_eq_free
end
end FourCorner.ProjectiveStabilizedDeterminant
