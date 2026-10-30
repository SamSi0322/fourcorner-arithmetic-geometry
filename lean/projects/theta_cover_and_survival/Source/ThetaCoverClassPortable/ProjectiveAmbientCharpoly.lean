import ThetaCoverClassPortable.ProjectiveNormBaseChange

/-! Free-ambient characteristic polynomials for actual finite-projective
retracts. Monicity never assumes the original module free or its rank
constant. The same-ambient conjugacy identity uses square charpoly_mul_comm. -/
namespace FourCorner.ProjectiveStabilizedDeterminant
open Polynomial
noncomputable section
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

 theorem charpoly_comp_comm {n : ℕ} (f g : Module.End R (Fin n → R)) :
    (f.comp g).charpoly=(g.comp f).charpoly := by
  rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun R (Fin n)),
    ← LinearMap.charpoly_toMatrix _ (Pi.basisFun R (Fin n)),
    LinearMap.toMatrix_comp (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)),
    LinearMap.toMatrix_comp (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n))]
  exact Matrix.charpoly_mul_comm _ _

/-- Two real split presentations in the SAME free ambient rank have the
same padded characteristic polynomial under actual operator conjugacy.
The source modules M,N need not be free, reduced, or constant-rank. -/
theorem ambient_charpoly_intertwiner {n : ℕ}
    (p : (Fin n → R) →ₗ[R] M) (i : M →ₗ[R] (Fin n → R)) (hp : p.comp i=LinearMap.id)
    (q : (Fin n → R) →ₗ[R] N) (j : N →ₗ[R] (Fin n → R)) (hq : q.comp j=LinearMap.id)
    (e : M ≃ₗ[R] N) (f : Module.End R M) (g : Module.End R N)
    (he : e.toLinearMap.comp f=g.comp e.toLinearMap) :
    (i.comp (f.comp p)).charpoly=(j.comp (g.comp q)).charpoly := by
  let U : Module.End R (Fin n → R) := i.comp (e.symm.toLinearMap.comp q)
  let V : Module.End R (Fin n → R) := j.comp (e.toLinearMap.comp (f.comp p))
  have hp' (x : M) : p (i x)=x := LinearMap.congr_fun hp x
  have hq' (x : N) : q (j x)=x := LinearMap.congr_fun hq x
  have hUV : U.comp V=i.comp (f.comp p) := by
    apply LinearMap.ext
    intro x
    simp only [U,V,LinearMap.comp_apply,LinearEquiv.coe_coe,hq',LinearEquiv.symm_apply_apply]
  have hVU : V.comp U=j.comp (g.comp q) := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun he (e.symm (q x))
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] at hx
    simp only [U,V,LinearMap.comp_apply,LinearEquiv.coe_coe,hp',hx]
  rw [← hUV,← hVU]
  exact charpoly_comp_comm U V

/-- Polynomial intertwining for arbitrary projective source modules; only
the ambient operator's characteristic polynomial later needs freeness. -/
theorem polynomial_intertwining {F : Type*} [AddCommGroup F] [Module R F]
    (u : Module.End R F) (v : Module.End R M) (i : M →ₗ[R] F)
    (hi : u.comp i=i.comp v) (P : R[X]) :
    (aeval u P).comp i=i.comp (aeval v P) := by
  induction P using Polynomial.induction_on with
  | C c =>
      simp only [aeval_C,Algebra.algebraMap_eq_smul_one]
      change (c • LinearMap.id).comp i=i.comp (c • LinearMap.id)
      rw [LinearMap.smul_comp,LinearMap.comp_smul,LinearMap.id_comp,LinearMap.comp_id]
  | add P Q hP hQ => rw [map_add,map_add,LinearMap.add_comp,LinearMap.comp_add,hP,hQ]
  | monomial n c hP =>
      simp only [pow_succ,← mul_assoc]
      have hu : aeval u (C c*X^n*X)=(aeval u (C c*X^n)).comp u := by rw [map_mul,aeval_X];rfl
      have hv : aeval v (C c*X^n*X)=(aeval v (C c*X^n)).comp v := by rw [map_mul,aeval_X];rfl
      rw [hu,hv,LinearMap.comp_assoc,hi,← LinearMap.comp_assoc,hP,LinearMap.comp_assoc]

 def ambientCharpoly (p : Frame R M) (f : Module.End R M) : R[X] :=
  (p.sectionMap.comp (f.comp p.projection)).charpoly
 theorem ambientCharpoly_monic (p : Frame R M) (f : Module.End R M) : (ambientCharpoly p f).Monic :=
  LinearMap.charpoly_monic _

/-- Actual Cayley–Hamilton restricts from R^m back to the given projective
module through the real split inclusion. No projective charpoly is postulated. -/
theorem ambientCharpoly_annihilates (p : Frame R M) (f : Module.End R M) :
    aeval f (ambientCharpoly p f)=0 := by
  let u := p.sectionMap.comp (f.comp p.projection)
  have hi : u.comp p.sectionMap=p.sectionMap.comp f := by
    apply LinearMap.ext
    intro x
    simp only [u,LinearMap.comp_apply,split_apply]
  have h := polynomial_intertwining u f p.sectionMap hi u.charpoly
  rw [LinearMap.aeval_self_charpoly,LinearMap.zero_comp] at h
  apply LinearMap.ext
  intro x
  apply (Function.LeftInverse.injective (fun y=>split_apply p y))
  have hx := LinearMap.congr_fun h x
  simpa only [ambientCharpoly,u,LinearMap.zero_apply,LinearMap.comp_apply,map_zero] using hx.symm

#print axioms ambient_charpoly_intertwiner
#print axioms ambientCharpoly_monic
#print axioms ambientCharpoly_annihilates
end
end FourCorner.ProjectiveStabilizedDeterminant
