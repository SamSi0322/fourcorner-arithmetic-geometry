import ThetaCoverClassPortable.FiniteRelationTraceDescent

namespace FourCorner.FiniteRelationQuotient
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]

 def traceReynolds (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (p : letI := s.toAlgebra;Frame A B) (u : Cˣ) : A →ₗ[C] C :=
  (↑u⁻¹ : C) • invariantTrace s t hgen heq hinj hinv p

 theorem traceReynolds_spec (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (p : letI := s.toAlgebra;Frame A B) (u : Cˣ) (a : A) :
    algebraMap C A (traceReynolds s t hgen heq hinj hinv p u a)=
      algebraMap C A (↑u⁻¹ : C)*sourceTrace s p (t a) := by
  simp only [traceReynolds,LinearMap.smul_apply,smul_eq_mul,map_mul,invariantTrace_spec]

/-- Actual normalized trace gives a C-linear retraction of the original
invariant inclusion, once the actual source identity trace is the unit u.
The subsequent rank theorem DERIVES this normalization for Q-algebras. -/
theorem traceReynolds_retraction (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (p : letI := s.toAlgebra;Frame A B) (u : Cˣ)
    (htrace : letI := s.toAlgebra;traceAlong p LinearMap.id=algebraMap C A (u : C)) :
    (traceReynolds s t hgen heq hinj hinv p u).comp (Algebra.linearMap C A)=LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply hinj
  change algebraMap C A (traceReynolds s t hgen heq hinj hinv p u (algebraMap C A c))=algebraMap C A c
  rw [traceReynolds_spec,← (hinv _).mpr ⟨c,rfl⟩,sourceTrace_source,htrace]
  rw [mul_left_comm,← map_mul,Units.inv_mul,map_one,mul_one]

 def relationDifference (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A)) :
    letI := relationAlgebra (C:=C) s; A →ₗ[C] B := by
  letI := relationAlgebra (C:=C) s
  exact (targetAlg s t hinv).toLinearMap-(sourceAlg (C:=C) s).toLinearMap

/-- The explicit true contracting homotopy h=−u⁻¹ Tr_s. -/
def traceHomotopy (s : A →+* B) (p : letI := s.toAlgebra;Frame A B) (u : Cˣ) :
    letI := relationAlgebra (C:=C) s; B →ₗ[C] A := by
  letI := relationAlgebra (C:=C) s
  exact -(↑u⁻¹ : C) • sourceTraceC s p

 theorem traceHomotopy_identity (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (p : letI := s.toAlgebra;Frame A B) (u : Cˣ)
    (htrace : letI := s.toAlgebra;traceAlong p LinearMap.id=algebraMap C A (u : C)) :
    letI := relationAlgebra (C:=C) s
    (traceHomotopy s p u).comp (relationDifference s t hinv)=
      LinearMap.id-(Algebra.linearMap C A).comp (traceReynolds s t hgen heq hinj hinv p u) := by
  letI := relationAlgebra (C:=C) s
  apply LinearMap.ext
  intro a
  change (-(↑u⁻¹ : C)) • sourceTrace s p (t a-s a)=
    a-algebraMap C A (traceReynolds s t hgen heq hinj hinv p u a)
  rw [map_sub,sourceTrace_source,htrace,traceReynolds_spec,Algebra.smul_def,map_neg]
  have hu : algebraMap C A (↑u⁻¹ : C)*algebraMap C A (u : C)=1 := by
    rw [← map_mul,Units.inv_mul,map_one]
  calc
    -algebraMap C A (↑u⁻¹ : C)*(sourceTrace s p (t a)-a*algebraMap C A (u : C))=
        a*(algebraMap C A (↑u⁻¹ : C)*algebraMap C A (u : C))-
          algebraMap C A (↑u⁻¹ : C)*sourceTrace s p (t a) := by ring
    _ = _ := by rw [hu,mul_one]

#print axioms traceReynolds_retraction
#print axioms traceHomotopy_identity
end
end FourCorner.FiniteRelationQuotient
