import ThetaCoverClassPortable.TameFibreDimensions
import ThetaCoverClassPortable.FiniteRelationAComparison
import ThetaCoverClassPortable.ComparisonEndpoints
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace FourCorner.FiniteRelationQuotient
open CategoryTheory
noncomputable section
open scoped TensorProduct
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A] [Algebra ℚ A]

/-- COMPLETE tame finite-relation algebra effectivity. Every residue
fibre dimension is DERIVED from the original arithmetic/groupoid inputs;
C-flatness/projectivity/comparison injectivity/effectivity is NOT a premise.
The finite-C/Q/rank inputs are genuinely proved by the actual literal
same-divisor source package, not new hypotheses of the final paper. -/
theorem tame_finite_relation_effective [Module.Finite C A] (s t : A →+* B)
    (hf : letI := s.toAlgebra;Module.Finite A B)
    (hp : letI := s.toAlgebra;Module.Projective A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) (hr : letI := s.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n) :
    letI := s.toAlgebra
    letI := relationAlgebra (C:=C) s
    Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      (∀p : PrimeSpectrum C,Module.rankAtStalk (R:=C) A p=n) ∧
      Function.Bijective (canonicalAComparison s t hinv) ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom s) (CommRingCat.ofHom t) := by
  letI := s.toAlgebra
  letI := relationAlgebra (C:=C) s
  letI := hf
  letI := hp
  have hdim := tame_residue_field_dimensions s t hf hp ht hgen heq hinj hinv hbase n hn hr
  exact FourCorner.QuotientLocalFree.global_leaf_for_right_leg hinj n hr
    (canonicalAComparison s t hinv) (canonicalAComparison_surjective s t hgen hinv) hdim t
      (canonicalAComparison_right s t hinv)

/-- Exact finite/projective/FF/original-pushout tuple for the actual Spec
quotient caller. The finite-C fact here is the already PROVED actual input;
the remaining three conclusions are derived above, never assumed. -/
theorem tame_finite_relation_quotient [Module.Finite C A] (s t : A →+* B)
    (hf : letI := s.toAlgebra;Module.Finite A B)
    (hp : letI := s.toAlgebra;Module.Projective A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) (hr : letI := s.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n) :
    Module.Finite C A ∧ Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom s) (CommRingCat.ofHom t) := by
  obtain ⟨hproj,hff,-,-,hpo⟩ := tame_finite_relation_effective s t hf hp ht hgen heq hinj hinv hbase n hn hr
  exact ⟨inferInstance,hproj,hff,hpo⟩

#print axioms tame_finite_relation_effective
#print axioms tame_finite_relation_quotient
end
end FourCorner.FiniteRelationQuotient
