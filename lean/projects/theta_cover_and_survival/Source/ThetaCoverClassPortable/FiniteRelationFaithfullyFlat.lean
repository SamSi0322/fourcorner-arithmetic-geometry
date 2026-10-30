import ThetaCoverClassPortable.FiniteRelationStructure

namespace FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- A flat ring map with an actual ring retraction is faithfully flat.
Surjectivity is proved on actual prime spectra, not assumed. -/
theorem faithfullyFlat_of_retraction (f : A →+* B) (e : B →+* A)
    (he : e.comp f=RingHom.id A)
    (hflat : letI := f.toAlgebra;Module.Flat A B) :
    letI := f.toAlgebra;Module.FaithfullyFlat A B := by
  letI := f.toAlgebra
  letI : Module.Flat A B := hflat
  apply Module.FaithfullyFlat.of_comap_surjective
  intro P
  refine ⟨PrimeSpectrum.comap e P,?_⟩
  change PrimeSpectrum.comap f (PrimeSpectrum.comap e P)=P
  rw [← PrimeSpectrum.comap_comp_apply,he]
  rfl

theorem source_injective (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : Function.Injective s := by
  intro a b hab
  have hh := congrArg (diagonal s t heq) hab
  change ((diagonal s t heq).comp s) a=((diagonal s t heq).comp s) b at hh
  simpa only [diagonal_source,RingHom.id_apply] using hh

theorem target_injective (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : Function.Injective t := by
  intro a b hab
  have hh := congrArg (diagonal s t heq) hab
  change ((diagonal s t heq).comp t) a=((diagonal s t heq).comp t) b at hh
  simpa only [diagonal_target,RingHom.id_apply] using hh

/-- The original source A→B is faithfully flat from the GIVEN projectivity
and the derived actual diagonal. This is not flatness of the sought C→A. -/
theorem source_faithfullyFlat (s t : A →+* B)
    (hproj : letI := s.toAlgebra;Module.Projective A B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    letI := s.toAlgebra;Module.FaithfullyFlat A B := by
  letI := s.toAlgebra
  letI : Module.Projective A B := hproj
  exact faithfullyFlat_of_retraction s (diagonal s t heq) (diagonal_source s t heq) inferInstance

theorem target_faithfullyFlat (s t : A →+* B)
    (hproj : letI := t.toAlgebra;Module.Projective A B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    letI := t.toAlgebra;Module.FaithfullyFlat A B := by
  letI := t.toAlgebra
  letI : Module.Projective A B := hproj
  exact faithfullyFlat_of_retraction t (diagonal s t heq) (diagonal_target s t heq) inferInstance

#print axioms faithfullyFlat_of_retraction
#print axioms source_injective
#print axioms target_injective
#print axioms source_faithfullyFlat
#print axioms target_faithfullyFlat
end
end FourCorner.FiniteRelationQuotient
