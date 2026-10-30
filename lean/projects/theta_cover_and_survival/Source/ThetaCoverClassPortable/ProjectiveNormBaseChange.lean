import ThetaCoverClassPortable.ProjectiveNormTransport
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

namespace FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Type w) [CommRing S] [Algebra R S]

 def freeBaseEquiv (n : ℕ) : S ⊗[R] (Fin n → R) ≃ₗ[S] (Fin n → S) :=
  TensorProduct.piScalarRight R S S (Fin n)

 def baseChangeFrame (p : Frame R M) : Frame S (S ⊗[R] M) where
  size := p.size
  projection := (p.projection.baseChange S).comp (freeBaseEquiv S p.size).symm.toLinearMap
  sectionMap := (freeBaseEquiv S p.size).toLinearMap.comp (p.sectionMap.baseChange S)
  split := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    have hh := congrArg (fun f=>f.baseChange S) p.split
    rw [LinearMap.baseChange_comp,LinearMap.baseChange_id] at hh
    exact LinearMap.congr_fun hh x

 theorem conjugate_stabilization {F G N : Type*} [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G] [AddCommGroup N] [Module R N]
    (a : F →ₗ[R] N) (b : N →ₗ[R] F) (f : Module.End R N) (e : F ≃ₗ[R] G) :
    e.toLinearMap.comp ((b.comp (f.comp a)+(LinearMap.id-b.comp a)).comp e.symm.toLinearMap)=
      (e.toLinearMap.comp b).comp (f.comp (a.comp e.symm.toLinearMap))+
        (LinearMap.id-(e.toLinearMap.comp b).comp (a.comp e.symm.toLinearMap)) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.id_apply,
    LinearEquiv.coe_coe,map_add,map_sub,LinearEquiv.apply_symm_apply]

 theorem stabilization_baseChange (p : Frame R M) (f : Module.End R M) :
    stabilize (baseChangeFrame S p) (f.baseChange S)=
      (freeBaseEquiv S p.size).toLinearMap.comp
        (((stabilize p f).baseChange S).comp (freeBaseEquiv S p.size).symm.toLinearMap) := by
  dsimp only [stabilize,baseChangeFrame]
  simp only [LinearMap.baseChange_add,LinearMap.baseChange_sub,LinearMap.baseChange_comp,LinearMap.baseChange_id]
  exact (conjugate_stabilization (p.projection.baseChange S) (p.sectionMap.baseChange S)
    (f.baseChange S) (freeBaseEquiv S p.size)).symm

/-- Genuine norm base change over EVERY commutative scalar ring, without
flatness of S/R or freeness of the original projective module M. -/
theorem normAlong_baseChange (p : Frame R M) (f : Module.End R M) :
    normAlong (baseChangeFrame S p) (f.baseChange S)=algebraMap R S (normAlong p f) := by
  have hs := stabilization_baseChange S p f
  have hd := congrArg (fun u : Module.End S (Fin p.size → S)=>LinearMap.det u) hs
  change LinearMap.det (stabilize (baseChangeFrame S p) (f.baseChange S))=
    algebraMap R S (LinearMap.det (stabilize p f))
  exact (hd.trans (LinearMap.det_conj ((stabilize p f).baseChange S) (freeBaseEquiv S p.size))).trans
    (LinearMap.det_baseChange (stabilize p f))

 theorem projective_tensor [Module.Finite R M] [Module.Projective R M] :
    Module.Projective S (S ⊗[R] M) := by
  let p := baseChangeFrame S (ofFiniteProjective R M)
  exact Module.Projective.of_split p.sectionMap p.projection p.split

/-- Choice-free mathematical scalar naturality of the constructed finite
projective norm, including polynomial base change and nilpotent scalars. -/
theorem norm_baseChange [Module.Finite R M] [Module.Projective R M] (f : Module.End R M) :
    letI := projective_tensor (R:=R) (M:=M) S
    norm S (S ⊗[R] M) (f.baseChange S)=algebraMap R S (norm R M f) := by
  letI := projective_tensor (R:=R) (M:=M) S
  exact (normAlong_independent (ofFiniteProjective S (S ⊗[R] M))
    (baseChangeFrame S (ofFiniteProjective R M)) _).trans (normAlong_baseChange S _ f)

#print axioms baseChangeFrame
#print axioms normAlong_baseChange
#print axioms projective_tensor
#print axioms norm_baseChange
end
end FourCorner.ProjectiveStabilizedDeterminant
