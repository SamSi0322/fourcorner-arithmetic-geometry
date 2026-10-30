import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Module.Projective
import Mathlib.Tactic.Abel

/-! A genuine determinant for finite projective modules obtained from an
actual finite-free retraction. Independence of that retraction is proved by
the rectangular Weinstein–Aronszajn determinant identity. This is necessary
norm infrastructure, not an assertion of the desired invariant quotient. -/
namespace FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Actual finite-free retraction data; construction below uses exactly
Module.Finite and Module.Projective, not a quotient-effectiveness premise. -/
structure Frame where
  size : ℕ
  projection : (Fin size → R) →ₗ[R] M
  sectionMap : M →ₗ[R] (Fin size → R)
  split : projection.comp sectionMap=LinearMap.id

 def ofFiniteProjective [Module.Finite R M] [Module.Projective R M] : Frame R M := by
  have h : Nonempty (Frame R M) := by
    obtain ⟨n,p,hp⟩ := Module.Finite.exists_fin' R M
    obtain ⟨i,hi⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
    exact ⟨⟨n,p,i,hi⟩⟩
  exact Classical.choice h

variable {R M}
 theorem split_apply (p : Frame R M) (m : M) : p.projection (p.sectionMap m)=m :=
  LinearMap.congr_fun p.split m

 def stabilize (p : Frame R M) (f : Module.End R M) : Module.End R (Fin p.size → R) :=
  p.sectionMap.comp (f.comp p.projection)+(LinearMap.id-p.sectionMap.comp p.projection)

 theorem stabilize_id (p : Frame R M) : stabilize p LinearMap.id=LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [stabilize]

 theorem stabilize_comp (p : Frame R M) (f g : Module.End R M) :
    stabilize p (f.comp g)=(stabilize p f).comp (stabilize p g) := by
  apply LinearMap.ext
  intro x
  simp only [stabilize,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.id_apply,map_add,map_sub,split_apply]
  abel

 def stabilization (p : Frame R M) : Module.End R M →* Module.End R (Fin p.size → R) where
  toFun := stabilize p
  map_one' := stabilize_id p
  map_mul' := stabilize_comp p

 def normAlong (p : Frame R M) : Module.End R M →* R := LinearMap.det.comp (stabilization p)

/-- Rectangular determinant identity for actual finite free linear maps,
valid over arbitrary commutative rings, including nilpotents and the zero ring. -/
theorem det_one_add_comp {n m : ℕ} (f : (Fin n → R) →ₗ[R] (Fin m → R))
    (g : (Fin m → R) →ₗ[R] (Fin n → R)) :
    LinearMap.det (LinearMap.id+f.comp g)=LinearMap.det (LinearMap.id+g.comp f) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun R (Fin m)),← LinearMap.det_toMatrix (Pi.basisFun R (Fin n))]
  simp only [map_add,LinearMap.toMatrix_id]
  rw [LinearMap.toMatrix_comp (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin m)),
    LinearMap.toMatrix_comp (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n))]
  exact Matrix.det_one_add_mul_comm _ _

 theorem stabilize_as_one_add (p : Frame R M) (f : Module.End R M) :
    stabilize p f=LinearMap.id+p.sectionMap.comp ((f-LinearMap.id).comp p.projection) := by
  apply LinearMap.ext
  intro x
  simp only [stabilize,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.comp_apply,
    LinearMap.id_apply,map_sub]
  abel

/-- Choice independence: neither projective complement, finite free size,
section nor projection is an assumed invariant. -/
theorem normAlong_independent (p q : Frame R M) (f : Module.End R M) :
    normAlong p f=normAlong q f := by
  let a : (Fin q.size → R) →ₗ[R] (Fin p.size → R) :=
    p.sectionMap.comp ((f-LinearMap.id).comp q.projection)
  let b : (Fin p.size → R) →ₗ[R] (Fin q.size → R) := q.sectionMap.comp p.projection
  have hab : a.comp b=p.sectionMap.comp ((f-LinearMap.id).comp p.projection) := by
    apply LinearMap.ext
    intro x
    simp only [a,b,LinearMap.comp_apply,split_apply]
  have hba : b.comp a=q.sectionMap.comp ((f-LinearMap.id).comp q.projection) := by
    apply LinearMap.ext
    intro x
    simp only [a,b,LinearMap.comp_apply,split_apply]
  change LinearMap.det (stabilize p f)=LinearMap.det (stabilize q f)
  rw [stabilize_as_one_add,stabilize_as_one_add,← hab,← hba]
  exact det_one_add_comp a b

/-- Actual finite-projective endomorphism norm; multiplicativity comes from
proved stabilization and independence is supplied above. -/
def norm (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] : Module.End R M →* R :=
  normAlong (ofFiniteProjective R M)

#print axioms ofFiniteProjective
#print axioms stabilize_comp
#print axioms normAlong_independent
#print axioms norm
end
end FourCorner.ProjectiveStabilizedDeterminant
