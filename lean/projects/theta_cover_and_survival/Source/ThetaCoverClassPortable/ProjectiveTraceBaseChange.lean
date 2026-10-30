import ThetaCoverClassPortable.ProjectiveTrace

namespace FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- True finite-projective trace commutes with arbitrary scalar change,
including nonflat residue-field base change and nilpotent scalar rings. -/
theorem traceAlong_baseChange (S : Type w) [CommRing S] [Algebra R S]
    (p : Frame R M) (f : Module.End R M) :
    traceAlong (baseChangeFrame S p) (f.baseChange S)=
      algebraMap R S (traceAlong p f) := by
  let e := freeBaseEquiv (R:=R) S p.size
  let u := p.sectionMap.comp (f.comp p.projection)
  have h : (baseChangeFrame S p).sectionMap.comp ((f.baseChange S).comp (baseChangeFrame S p).projection)=
      e.toLinearMap.comp ((u.baseChange S).comp e.symm.toLinearMap) := by
    dsimp only [baseChangeFrame,e,u]
    simp only [LinearMap.baseChange_comp,LinearMap.comp_assoc]
    rfl
  change LinearMap.trace S _ ((baseChangeFrame S p).sectionMap.comp
    ((f.baseChange S).comp (baseChangeFrame S p).projection))=
      algebraMap R S (LinearMap.trace R _ u)
  rw [h,← LinearMap.comp_assoc]
  have he : LinearMap.trace S _ ((e.toLinearMap.comp (u.baseChange S)).comp e.symm.toLinearMap)=
      LinearMap.trace S _ (u.baseChange S) := by
    simpa only [LinearEquiv.conj_apply] using (LinearMap.trace_conj' (u.baseChange S) e)
  exact he.trans (LinearMap.trace_baseChange u S)

 theorem projectiveTrace_baseChange [Module.Finite R M] [Module.Projective R M]
    (S : Type w) [CommRing S] [Algebra R S] (f : Module.End R M) :
    letI := projective_tensor (R:=R) (M:=M) S
    projectiveTrace (R:=S) (M:=S ⊗[R] M) (f.baseChange S)=
      algebraMap R S (projectiveTrace (R:=R) (M:=M) f) := by
  letI := projective_tensor (R:=R) (M:=M) S
  exact (traceAlong_independent (ofFiniteProjective S (S ⊗[R] M))
    (baseChangeFrame S (ofFiniteProjective R M)) _).trans (traceAlong_baseChange S _ f)

#print axioms traceAlong_baseChange
#print axioms projectiveTrace_baseChange
end
end FourCorner.ProjectiveStabilizedDeterminant
