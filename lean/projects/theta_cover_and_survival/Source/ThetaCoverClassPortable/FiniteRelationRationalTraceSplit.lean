import ThetaCoverClassPortable.FiniteRelationTraceSplitting
import ThetaCoverClassPortable.ProjectiveTraceRank
import ThetaCoverClassPortable.SplitLinearEqualizerBaseChange

namespace FourCorner.FiniteRelationQuotient
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
universe u v
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]
variable [Algebra ℚ A]

/-- Construct the actual rational base in the exact invariant C. -/
def rationalInvariantMap (s t : A →+* B)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A)) : ℚ →+* C :=
  (invariantRingEquiv s t hinj hinv).symm.toRingHom.comp
    ((algebraMap ℚ A).codRestrict (s.eqLocus t) (fun q=>RingHom.congr_fun hbase q))

 def positiveRankUnit (s t : A →+* B)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) : Cˣ :=
  Units.map (rationalInvariantMap s t hinj hinv hbase).toMonoidHom
    (Units.mk0 (n : ℚ) (Nat.cast_ne_zero.mpr hn))

 theorem positiveRankUnit_coe (s t : A →+* B)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) :
    (positiveRankUnit s t hinj hinv hbase n hn : C)=(n : C) := by
  change rationalInvariantMap s t hinj hinv hbase (n : ℚ)=(n : C)
  exact map_natCast _ n

 theorem relationDifference_inclusion (s t : A →+* B)
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A)) :
    letI := relationAlgebra (C:=C) s
    (relationDifference s t hinv).comp (Algebra.linearMap C A)=0 := by
  letI := relationAlgebra (C:=C) s
  apply LinearMap.ext
  intro c
  change t (algebraMap C A c)-s (algebraMap C A c)=0
  exact sub_eq_zero.mpr ((hinv _).mpr ⟨c,rfl⟩).symm

/-- COMPLETE step1 for the actual tame constant-rank specialization:
original finite-projective all-ring relation plus a common rational base
and actual nonzero constant rank DERIVE the split invariant equalizer.
No split/projection/flat-C/effectivity conclusion is added as a premise. -/
theorem rational_constantRank_split (s t : A →+* B)
    (hfinite : letI := s.toAlgebra;Module.Finite A B)
    (hprojective : letI := s.toAlgebra;Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0)
    (hrank : letI := s.toAlgebra;∀q : PrimeSpectrum A,Module.rankAtStalk B q=n) :
    letI := relationAlgebra (C:=C) s
    ∃ (P : A →ₗ[C] C) (H : B →ₗ[C] A),
      P.comp (Algebra.linearMap C A)=LinearMap.id ∧
      H.comp (relationDifference s t hinv)=LinearMap.id-(Algebra.linearMap C A).comp P := by
  letI := s.toAlgebra
  letI := hfinite
  letI := hprojective
  letI := relationAlgebra (C:=C) s
  let p := ofFiniteProjective A B
  let u := positiveRankUnit s t hinj hinv hbase n hn
  have ht : traceAlong p LinearMap.id=algebraMap C A (u : C) := by
    simpa only [u,positiveRankUnit_coe,map_natCast] using (traceAlong_id_of_rankAtStalk p n hrank)
  exact ⟨traceReynolds s t hgen heq hinj hinv p u,traceHomotopy s p u,
    traceReynolds_retraction s t hgen heq hinj hinv p u ht,
    traceHomotopy_identity s t hgen heq hinj hinv p u ht⟩

/-- Actual invariant equalizer is preserved by EVERY scalar extension,
without presuming that scalar extension flat. In particular this applies
to all residue fields and their algebraic closures. -/
theorem rational_constantRank_baseChange_invariants (s t : A →+* B)
    (hfinite : letI := s.toAlgebra;Module.Finite A B)
    (hprojective : letI := s.toAlgebra;Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0)
    (hrank : letI := s.toAlgebra;∀q : PrimeSpectrum A,Module.rankAtStalk B q=n)
    (S : Type v) [CommRing S] [Algebra C S] :
    letI := relationAlgebra (C:=C) s
    LinearMap.range ((Algebra.linearMap C A).baseChange S)=
      LinearMap.ker ((relationDifference s t hinv).baseChange S) := by
  letI := relationAlgebra (C:=C) s
  obtain ⟨P,H,-,hhd⟩ := rational_constantRank_split s t hfinite hprojective hgen heq hinj hinv hbase n hn hrank
  exact FourCorner.SplitLinearEqualizerBaseChange.baseChange_range_eq_ker
    (Algebra.linearMap C A) (relationDifference s t hinv) P H (relationDifference_inclusion s t hinv) hhd S

#print axioms rational_constantRank_split
#print axioms rational_constantRank_baseChange_invariants
end
end FourCorner.FiniteRelationQuotient
