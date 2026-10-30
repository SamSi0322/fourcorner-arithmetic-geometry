import ThetaCoverClassPortable.FiniteRelationInvariantTrace
import ThetaCoverClassPortable.FiniteRelationComparison

namespace FourCorner.FiniteRelationQuotient
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]

 def sourceTraceC (s : A →+* B) (p : letI := s.toAlgebra;Frame A B) :
    letI := relationAlgebra (C:=C) s;B →ₗ[C] A := by
  letI := s.toAlgebra
  letI := relationAlgebra (C:=C) s
  letI : IsScalarTower C A B := IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  exact (sourceTrace s p).restrictScalars C

 def targetTraceC (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (p : letI := s.toAlgebra;Frame A B) : A →ₗ[C] A := by
  letI := relationAlgebra (C:=C) s
  exact (sourceTraceC (C:=C) s p).comp (targetAlg s t hinv).toLinearMap

/-- True coefficient descent of the actual trace to the EXACT embedded
invariant C, as a C-linear map. No Reynolds operator is assumed. -/
def invariantTrace (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (p : letI := s.toAlgebra;Frame A B) : A →ₗ[C] C := by
  let e := LinearEquiv.ofInjective (Algebra.linearMap C A) hinj
  let f := targetTraceC s t hinv p
  have hf : ∀a,f a∈LinearMap.range (Algebra.linearMap C A) := by
    intro a
    change f a∈Set.range (algebraMap C A)
    exact (hinv _).mp (sourceTrace_target_invariant s t hgen heq p a)
  exact e.symm.toLinearMap.comp (f.codRestrict _ hf)

 theorem invariantTrace_spec (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (p : letI := s.toAlgebra;Frame A B) (a : A) :
    algebraMap C A (invariantTrace s t hgen heq hinj hinv p a)=sourceTrace s p (t a) := by
  let e := LinearEquiv.ofInjective (Algebra.linearMap C A) hinj
  exact congrArg Subtype.val (e.apply_symm_apply _)

#print axioms invariantTrace
#print axioms invariantTrace_spec
end
end FourCorner.FiniteRelationQuotient
