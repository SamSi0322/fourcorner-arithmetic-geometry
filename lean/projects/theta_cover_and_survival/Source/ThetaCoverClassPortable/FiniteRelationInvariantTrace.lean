import ThetaCoverClassPortable.RingMapPushoutTrace
import ThetaCoverClassPortable.FiniteRelationTranslationAlgebra

namespace FourCorner.FiniteRelationQuotient
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- Actual A-linear trace on the original source algebra B_s. Native
trace is applied solely to the real finite free ambient presentation. -/
def sourceTrace (s : A →+* B) (p : letI := s.toAlgebra;Frame A B) :
    letI := s.toAlgebra; B →ₗ[A] A := by
  letI := s.toAlgebra
  exact (traceAlong p).comp (Algebra.lmul A B).toLinearMap

 theorem sourceTrace_source (s : A →+* B) (p : letI := s.toAlgebra;Frame A B) (a : A) :
    letI := s.toAlgebra
    sourceTrace s p (s a)=a*traceAlong p LinearMap.id := by
  letI := s.toAlgebra
  have hm : Algebra.lmul A B (s a)=a • (LinearMap.id : Module.End A B) := by
    apply LinearMap.ext
    intro b
    rfl
  change traceAlong p (Algebra.lmul A B (s a))=_
  rw [hm,map_smul]
  rfl

 theorem sourceTrace_target_invariant (s t : A →+* B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (p : letI := s.toAlgebra;Frame A B) (a : A) :
    s (sourceTrace s p (t a))=t (sourceTrace s p (t a)) := by
  letI := s.toAlgebra
  letI := sourcePairAlgebra s
  letI := composableAlgebra s t
  let ps := RingMapTensorPushout.pushoutFrame s s p
  let pt := RingMapTensorPushout.pushoutFrame t s p
  have h := traceAlong_intertwiner ps pt (translationAlgEquiv s t hgen heq).toLinearEquiv
    (LinearMap.mulLeft B ((sourceRight s).hom (t a)))
    (LinearMap.mulLeft B ((pairRight s t).hom (t a)))
    (translation_multiplication s t hgen heq a)
  have hm (b : B) : Algebra.lmul A B b=LinearMap.mulLeft A b := by
    apply LinearMap.ext
    intro z
    rfl
  change s (traceAlong p (Algebra.lmul A B (t a)))=t (traceAlong p (Algebra.lmul A B (t a)))
  rw [hm]
  exact (RingMapTensorPushout.traceAlong_pushout s s p (t a)).symm.trans
    (h.trans (RingMapTensorPushout.traceAlong_pushout t s p (t a)))

#print axioms sourceTrace_source
#print axioms sourceTrace_target_invariant
end
end FourCorner.FiniteRelationQuotient
