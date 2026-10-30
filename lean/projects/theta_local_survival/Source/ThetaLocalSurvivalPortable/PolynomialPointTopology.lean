import ThetaLocalSurvivalPortable.OpenImmersionPoints
import Mathlib.RingTheory.Extension.Presentation.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (R A K : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing K] [Algebra R K] [TopologicalSpace K] [IsTopologicalRing K]
variable {ι : Type*}

/-- Polynomial evaluation is jointly continuous in coefficient points and variable values. -/
theorem continuous_eval₂_point (p : MvPolynomial ι A) :
    Continuous (fun q : (A →ₐ[R] K) × (ι → K) => eval₂ q.1.toRingHom q.2 p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [eval₂_C]
      change Continuous (fun q : (A →ₐ[R] K) × (ι → K) => q.1 a)
      exact (continuous_evaluation R A K a).comp continuous_fst
  | add p q hp hq =>
      simp only [eval₂_add]
      exact hp.add hq
  | mul_X p i hp =>
      simp only [eval₂_mul,eval₂_X]
      exact hp.mul ((continuous_apply i).comp continuous_snd)

/-- Evaluation with a varying R-algebra coefficient map remains an actual R-algebra map. -/
def pointPolynomialEval (φ : A →ₐ[R] K) (x : ι → K) : MvPolynomial ι A →ₐ[R] K where
  __ := eval₂Hom φ.toRingHom x
  commutes' r := by
    change eval₂ φ.toRingHom x (C (algebraMap R A r)) = algebraMap R K r
    simp

variable (S : Type*) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
  {σ : Type*} (P : Algebra.Presentation A S ι σ)

/-- Actual solutions of the actual finite-presentation equations, with the subspace topology. -/
abbrev presentationSolutions :=
  {q : (A →ₐ[R] K) × (ι → K) // ∀ i, eval₂ q.1.toRingHom q.2 (P.relation i) = 0}

theorem eval₂_point_relation (f : S →ₐ[R] K) (i : σ) :
    eval₂ (f.comp (Algebra.algHom R A S)).toRingHom (fun j => f (P.val j)) (P.relation i)=0 := by
  have h := congrArg f (P.aeval_val_relation i)
  rw [map_zero] at h
  rw [MvPolynomial.aeval_def] at h
  change f.toRingHom (eval₂ (algebraMap A S) P.val (P.relation i))=0 at h
  rw [MvPolynomial.eval₂_comp_left] at h
  exact h

def presentationPointCoordinates (f : S →ₐ[R] K) : presentationSolutions R A K S P :=
  ⟨(f.comp (Algebra.algHom R A S),fun i => f (P.val i)),eval₂_point_relation R A K S P f⟩

def presentationSolutionLift (q : presentationSolutions R A K S P) : S →ₐ[R] K :=
  AlgHom.liftOfSurjective ((aeval P.val).restrictScalars R) P.aeval_val_surjective
    (pointPolynomialEval R A K q.1.1 q.1.2) (by
      intro p hp
      change aeval (R:=A) P.val p=0 at hp
      have hpker : p∈P.ker := by
        simpa only [P.ker_eq_ker_aeval_val,RingHom.mem_ker] using hp
      have hs : Ideal.span (Set.range P.relation) ≤
          RingHom.ker (pointPolynomialEval R A K q.1.1 q.1.2).toRingHom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        exact q.2 i
      exact hs (P.span_range_relation_eq_ker.symm ▸ hpker))


theorem presentationSolutionLift_aeval (q : presentationSolutions R A K S P)
    (p : MvPolynomial ι A) :
    presentationSolutionLift R A K S P q (aeval P.val p) = eval₂ q.1.1.toRingHom q.1.2 p :=
  AlgHom.liftOfSurjective_apply _ _ _ _ p

theorem presentationSolutionLift_apply (q : presentationSolutions R A K S P) (s : S) :
    presentationSolutionLift R A K S P q s = eval₂ q.1.1.toRingHom q.1.2 (P.σ s) := by
  rw [←presentationSolutionLift_aeval R A K S P q,P.aeval_val_σ]

def presentationPointEquiv : (S →ₐ[R] K) ≃ presentationSolutions R A K S P where
  toFun := presentationPointCoordinates R A K S P
  invFun := presentationSolutionLift R A K S P
  left_inv := by
    intro f
    ext s
    rw [presentationSolutionLift_apply]
    have h := congrArg f (P.aeval_val_σ s)
    rw [MvPolynomial.aeval_def] at h
    change f.toRingHom (eval₂ (algebraMap A S) P.val (P.σ s))=f s at h
    rw [MvPolynomial.eval₂_comp_left] at h
    exact h
  right_inv := by
    intro q
    apply Subtype.ext
    apply Prod.ext
    · ext a
      change presentationSolutionLift R A K S P q (algebraMap A S a)=q.1.1 a
      change presentationSolutionLift R A K S P q (algebraMap A S a)=q.1.1.toRingHom a
      have h := presentationSolutionLift_aeval R A K S P q (C a)
      simpa only [aeval_C,eval₂_C] using h
    · funext i
      change presentationSolutionLift R A K S P q (P.val i)=q.1.2 i
      have h := presentationSolutionLift_aeval R A K S P q (X i)
      simpa only [aeval_X,eval₂_X] using h

theorem continuous_presentationPointCoordinates : Continuous (presentationPointCoordinates R A K S P) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_precomposition _
  · exact continuous_pi (fun i => continuous_evaluation R S K (P.val i))

theorem continuous_presentationSolutionLift : Continuous (presentationSolutionLift R A K S P) := by
  apply (continuous_affine_iff R S K _).2
  intro s
  simp_rw [presentationSolutionLift_apply]
  exact (continuous_eval₂_point R A K (P.σ s)).comp continuous_subtype_val

/-- Exact presentation-coordinate homeomorphism; no symbolic replacement for S(K). -/
def presentationPointsHomeomorph : (S →ₐ[R] K) ≃ₜ presentationSolutions R A K S P where
  toEquiv := presentationPointEquiv R A K S P
  continuous_toFun := continuous_presentationPointCoordinates R A K S P
  continuous_invFun := continuous_presentationSolutionLift R A K S P

end FourCorner.ThetaLocalSurvival.StrongTopology
