import ThetaCoverClassPortable.FiniteScalarPointExtension
import ThetaCoverClassPortable.FiniteRelationTensorInvariants

namespace FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A] [Algebra ℚ A]

/-- Actual arbitrary field fibre is nonzero, DERIVED from the proved
normalized-trace split injection; no nonzero-fibre hypothesis is added. -/
theorem tame_field_fibre_nontrivial (s t : A →+* B)
    (hf : letI := s.toAlgebra;Module.Finite A B)
    (hp : letI := s.toAlgebra;Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) (hr : letI := s.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n)
    (K : Type u) [Field K] [Algebra C K] : Nontrivial (K ⊗[C] A) := by
  have hi := rational_constantRank_tensor_scalar_injective s t hf hp hgen heq hinj hinv hbase n hn hr K
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  exact one_ne_zero (hi (by simpa only [map_one,map_zero] using h))

/-- The actual tame relation inputs, exact invariant C and proved finite
C-extension supply a genuine finite residue field point of the DIRECT
fibre, with every guard and tensor identity proved internally. -/
theorem tame_exists_finite_point (s t : A →+* B)
    (hf : letI := s.toAlgebra;Module.Finite A B)
    (hp : letI := s.toAlgebra;Module.Projective A B)
    (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a,s a=t a ↔ a∈Set.range (algebraMap C A))
    (hbase : s.comp (algebraMap ℚ A)=t.comp (algebraMap ℚ A))
    (n : ℕ) (hn : n≠0) (hr : letI := s.toAlgebra;∀p : PrimeSpectrum A,Module.rankAtStalk B p=n)
    [Module.Finite C A] (K : Type u) [Field K] [Algebra C K] :
    ∃(L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L),
      letI : Algebra C L := ((algebraMap K L).comp (algebraMap C K)).toAlgebra
      ∃x : L ⊗[C] A →ₐ[L] L,Module.finrank L (L ⊗[C] A)=Module.finrank K (K ⊗[C] A) := by
  letI := tame_field_fibre_nontrivial s t hf hp hgen heq hinj hinv hbase n hn hr K
  exact FourCorner.FiniteResiduePointBaseChange.exists_finite_point_on_direct_scalar_change C A K

#print axioms tame_field_fibre_nontrivial
#print axioms tame_exists_finite_point
end
end FourCorner.FiniteRelationQuotient
