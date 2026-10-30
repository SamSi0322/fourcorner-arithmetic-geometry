import ThetaCoverClassPortable.ProjectiveAmbientCharpoly

namespace FourCorner.ProjectiveStabilizedDeterminant
open Polynomial
noncomputable section
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

 theorem ambientCharpoly_transport (p : Frame R M) (e : M ≃ₗ[R] N)
    (f : Module.End R M) (g : Module.End R N) (he : e.toLinearMap.comp f=g.comp e.toLinearMap) :
    ambientCharpoly (transportFrame p e) g=ambientCharpoly p f := by
  exact (ambient_charpoly_intertwiner p.projection p.sectionMap p.split
    (transportFrame p e).projection (transportFrame p e).sectionMap (transportFrame p e).split e f g he).symm

 theorem ambientCharpoly_baseChange (S : Type w) [CommRing S] [Algebra R S]
    (p : Frame R M) (f : Module.End R M) :
    ambientCharpoly (baseChangeFrame S p) (f.baseChange S)=
      (ambientCharpoly p f).map (algebraMap R S) := by
  let e := freeBaseEquiv (R:=R) S p.size
  let u := p.sectionMap.comp (f.comp p.projection)
  have h : (baseChangeFrame S p).sectionMap.comp ((f.baseChange S).comp (baseChangeFrame S p).projection)=
      e.toLinearMap.comp ((u.baseChange S).comp e.symm.toLinearMap) := by
    dsimp only [baseChangeFrame,e,u]
    simp only [LinearMap.baseChange_comp,LinearMap.comp_assoc]
    rfl
  have hc := congrArg (fun v : Module.End S (Fin p.size → S)=>v.charpoly) h
  have he : (e.toLinearMap.comp ((u.baseChange S).comp e.symm.toLinearMap)).charpoly=(u.baseChange S).charpoly := by
    rw [← LinearMap.comp_assoc]
    simpa only [LinearEquiv.conj_apply] using LinearEquiv.charpoly_conj e (u.baseChange S)
  exact (hc.trans he).trans (LinearMap.charpoly_baseChange u S)

#print axioms ambientCharpoly_transport
#print axioms ambientCharpoly_baseChange
end
end FourCorner.ProjectiveStabilizedDeterminant
