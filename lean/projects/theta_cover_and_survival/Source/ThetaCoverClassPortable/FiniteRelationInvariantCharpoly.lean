import ThetaCoverClassPortable.RingMapPushoutCharpoly
import ThetaCoverClassPortable.FiniteRelationTranslationAlgebra
import ThetaCoverClassPortable.FiniteRelationNorm

namespace FourCorner.FiniteRelationQuotient
open Polynomial FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- The real ambient characteristic polynomial of multiplication by the
original target coordinate on B with its SOURCE A-module structure. -/
def relationPolynomial (s t : A →+* B)
    (p : letI := s.toAlgebra; Frame A B) (a : A) : A[X] := by
  letI := s.toAlgebra
  exact ambientCharpoly p (LinearMap.mulLeft A (t a))

 theorem relationPolynomial_monic (s t : A →+* B)
    (p : letI := s.toAlgebra; Frame A B) (a : A) :
    (relationPolynomial s t p a).Monic := by
  letI := s.toAlgebra
  exact ambientCharpoly_monic p _

/-- Genuine all-ring groupoid translation forces equality of EVERY
coefficient after s and t, even at nilpotent collision fibres. -/
theorem relationPolynomial_invariant (s t : A →+* B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (p : letI := s.toAlgebra; Frame A B) (a : A) :
    (relationPolynomial s t p a).map s=(relationPolynomial s t p a).map t := by
  letI := s.toAlgebra
  letI := sourcePairAlgebra s
  letI := composableAlgebra s t
  let ps := RingMapTensorPushout.pushoutFrame s s p
  let pt := RingMapTensorPushout.pushoutFrame t s p
  have h := ambient_charpoly_intertwiner ps.projection ps.sectionMap ps.split
    pt.projection pt.sectionMap pt.split (translationAlgEquiv s t hgen heq).toLinearEquiv
    (LinearMap.mulLeft B ((sourceRight s).hom (t a)))
    (LinearMap.mulLeft B ((pairRight s t).hom (t a)))
    (translation_multiplication s t hgen heq a)
  change ambientCharpoly ps _=ambientCharpoly pt _ at h
  exact (RingMapTensorPushout.ambientCharpoly_pushout s s p (t a)).symm.trans
    (h.trans (RingMapTensorPushout.ambientCharpoly_pushout t s p (t a)))

/-- Restrict Cayley-Hamilton to the original module B, then apply the
proved diagonal B→A. No freeness of B/A is used. -/
theorem relationPolynomial_eval_self (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (p : letI := s.toAlgebra; Frame A B) (a : A) :
    (relationPolynomial s t p a).eval a=0 := by
  letI := s.toAlgebra
  let e : B →ₐ[A] A := augmentation s (diagonal s t heq) (diagonal_source s t heq)
  have h : aeval (t a) (relationPolynomial s t p a)=0 := by
    apply Algebra.lmul_injective (R:=A)
    have hm : Algebra.lmul A B (t a)=LinearMap.mulLeft A (t a) := by
      ext b; rfl
    simpa only [← aeval_algHom_apply, map_zero, hm, relationPolynomial] using
      (ambientCharpoly_annihilates p (LinearMap.mulLeft A (t a)))
  have hd : e (t a)=a := RingHom.congr_fun (diagonal_target s t heq) a
  have he := congrArg e h
  rw [← aeval_algHom_apply, hd, map_zero] at he
  simpa only [aeval_def, eval₂_at_apply, Algebra.algebraMap_self, eval₂_id] using he

#print axioms relationPolynomial_invariant
#print axioms relationPolynomial_eval_self
end
end FourCorner.FiniteRelationQuotient
