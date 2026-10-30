import ThetaCoverClassPortable.ProjectiveStabilizedDeterminant

namespace FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u v w
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- An actual module equivalence transports a genuine finite free retraction. -/
def transportFrame (p : Frame R M) (e : M ≃ₗ[R] N) : Frame R N where
  size := p.size
  projection := e.toLinearMap.comp p.projection
  sectionMap := p.sectionMap.comp e.symm.toLinearMap
  split := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,split_apply,LinearMap.id_apply]
    exact e.apply_symm_apply x

 theorem stabilization_transport (p : Frame R M) (e : M ≃ₗ[R] N) (f : Module.End R M) :
    stabilize (transportFrame p e) (e.toLinearMap.comp (f.comp e.symm.toLinearMap))=stabilize p f := by
  dsimp only [stabilize,transportFrame]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.id_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

 theorem normAlong_transport (p : Frame R M) (e : M ≃ₗ[R] N) (f : Module.End R M) :
    normAlong (transportFrame p e) (e.toLinearMap.comp (f.comp e.symm.toLinearMap))=normAlong p f := by
  change LinearMap.det (stabilize (transportFrame p e) (e.toLinearMap.comp (f.comp e.symm.toLinearMap)))=
    LinearMap.det (stabilize p f)
  rw [stabilization_transport]
  rfl

/-- The finite-projective norm is invariant under ACTUAL module conjugacy;
no global freeness or choice-compatibility hypothesis is required. -/
theorem norm_conjugate [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (e : M ≃ₗ[R] N) (f : Module.End R M) :
    norm R N (e.toLinearMap.comp (f.comp e.symm.toLinearMap))=norm R M f := by
  exact (normAlong_independent (ofFiniteProjective R N)
    (transportFrame (ofFiniteProjective R M) e) _).trans (normAlong_transport _ e f)

#print axioms transportFrame
#print axioms norm_conjugate
end
end FourCorner.ProjectiveStabilizedDeterminant
