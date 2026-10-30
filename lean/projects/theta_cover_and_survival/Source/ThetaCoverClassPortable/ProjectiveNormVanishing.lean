import ThetaCoverClassPortable.ProjectiveStabilizedDeterminant

namespace FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u v
variable {R : Type u} [CommRing R]

/-- A unimodular left annihilator forces the ACTUAL finite-free determinant
to vanish. The adjugate proof is valid for arbitrary nilpotent scalars. -/
theorem det_zero_of_left_annihilator {n : ℕ} (f : Module.End R (Fin n → R))
    (l : (Fin n → R) →ₗ[R] R) (v : Fin n → R) (hv : l v=1)
    (hf : l.comp f=0) : LinearMap.det f=0 := by
  let a : Module.End R (Fin n → R) := Matrix.toLin' (LinearMap.toMatrix' f).adjugate
  have hfa : f.comp a=LinearMap.det f • LinearMap.id := by
    apply (LinearMap.toMatrix' : Module.End R (Fin n → R) ≃ₗ[R] Matrix (Fin n) (Fin n) R).injective
    simp only [LinearMap.toMatrix'_comp,a,LinearMap.toMatrix'_toLin',map_smul,LinearMap.toMatrix'_id]
    rw [Matrix.mul_adjugate,LinearMap.det_toMatrix']
  have hzero : l (f (a v))=0 := by
    exact LinearMap.congr_fun hf (a v)
  have he : f (a v)=LinearMap.det f • v := LinearMap.congr_fun hfa v
  rw [he,map_smul,hv,smul_eq_mul,mul_one] at hzero
  exact hzero

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Vanishing of the finite-projective norm follows from a genuine split
rank-one quotient annihilated by the endomorphism; no basis of M is assumed. -/
theorem normAlong_zero_of_left_annihilator (p : Frame R M) (f : Module.End R M)
    (l : M →ₗ[R] R) (v : M) (hv : l v=1) (hf : l.comp f=0) : normAlong p f=0 := by
  let L := l.comp p.projection
  have hL : L.comp (stabilize p f)=0 := by
    apply LinearMap.ext
    intro x
    have hlf : l (f (p.projection x))=0 := LinearMap.congr_fun hf (p.projection x)
    simp only [L,stabilize,LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,
      LinearMap.id_apply,map_add,map_sub,split_apply,hlf,zero_add,sub_self,LinearMap.zero_apply]
  have hLv : L (p.sectionMap v)=1 := by
    change l (p.projection (p.sectionMap v))=1
    rw [split_apply,hv]
  exact det_zero_of_left_annihilator (stabilize p f) L (p.sectionMap v) hLv hL

 theorem norm_zero_of_left_annihilator [Module.Finite R M] [Module.Projective R M]
    (f : Module.End R M) (l : M →ₗ[R] R) (v : M) (hv : l v=1) (hf : l.comp f=0) :
    norm R M f=0 := normAlong_zero_of_left_annihilator (ofFiniteProjective R M) f l v hv hf

#print axioms det_zero_of_left_annihilator
#print axioms norm_zero_of_left_annihilator
end
end FourCorner.ProjectiveStabilizedDeterminant
