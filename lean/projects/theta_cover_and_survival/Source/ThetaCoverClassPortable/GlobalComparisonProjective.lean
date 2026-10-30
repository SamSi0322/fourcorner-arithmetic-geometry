import ThetaCoverClassPortable.ComparisonScalarChange
import ThetaCoverClassPortable.Theorems.Thm_Module_finitePresentation_of_rankAtStalk_eq
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Rank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
namespace FourCorner.QuotientLocalFree
universe u
variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra A B] [Module.Finite C A]
  [Module.Finite A B] [Module.Projective A B]

/-- Real local bases at EVERY prime of C, obtained by genuine scalar extension
of the given comparison. Flatness of A/C is a conclusion, never an input. -/
theorem basis_atPrime (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n)
    (p : PrimeSpectrum C) :
    Nonempty (Module.Basis (Fin n) (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[C] A)) := by
  let S := Localization.AtPrime p.asIdeal
  let AS := S ⊗[C] A
  letI : Algebra A AS := Algebra.TensorProduct.rightAlgebra
  let BS := AS ⊗[A] B
  haveI : Module.Finite S AS := inferInstance
  haveI : Module.Finite AS BS := inferInstance
  haveI : Module.Projective AS BS := inferInstance
  haveI : Module.Flat A B := inferInstance
  have hrankS (q : PrimeSpectrum AS) : Module.rankAtStalk (R := AS) BS q = n :=
    (Module.rankAtStalk_baseChange q).trans (hrank _)
  have hinjS : Function.Injective (algebraMap S AS) :=
    inclusion_injective_after_flat_scalar_change S hinj
  let CanS := comparisonBaseChange S Can
  have hsurjS : Function.Surjective CanS := comparisonBaseChange_surjective S Can hCan
  have hdimS : Module.finrank (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S ⊗[S] AS) = n := by
    let E := Algebra.TensorProduct.cancelBaseChange C S (IsLocalRing.ResidueField S)
      (IsLocalRing.ResidueField S) A
    exact E.toLinearEquiv.finrank_eq.trans (hdim p)
  obtain ⟨b, _⟩ := local_free_and_comparison_bijective hinjS n hrankS CanS hsurjS hdimS
  exact ⟨b⟩

theorem rankAtStalk_eq (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n)
    (p : PrimeSpectrum C) : Module.rankAtStalk (R := C) A p = n := by
  classical
  obtain ⟨b⟩ := basis_atPrime hinj n hrank Can hCan hdim p
  change Module.finrank (Localization.AtPrime p.asIdeal)
    (LocalizedModule p.asIdeal.primeCompl A) = n
  rw [(LocalizedModule.equivTensorProduct p.asIdeal.primeCompl A).finrank_eq]
  simpa using Module.finrank_eq_card_basis b

theorem flat_of_residue_rank (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n) :
    Module.Flat C A := by
  apply Module.flat_of_localized_maximal A
  intro p _
  let S := Localization.AtPrime p
  let AS := S ⊗[C] A
  obtain ⟨b⟩ := basis_atPrime hinj n hrank Can hCan hdim ⟨p, inferInstance⟩
  haveI : Module.Free S AS := Module.Free.of_basis b
  haveI : Module.Flat S AS := inferInstance
  haveI : Module.Flat C AS := Module.Flat.trans C S AS
  exact Module.Flat.of_linearEquiv ((LocalizedModule.equivTensorProduct p.primeCompl A).restrictScalars C)

/-- All global conclusions of the generic algebraic leaf. Zero C is retained:
stalk rank is quantified on Spec C, never replaced by a false global finrank claim. -/
theorem projective_ff_comparison (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n) :
    Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      (∀ p : PrimeSpectrum C, Module.rankAtStalk (R := C) A p = n) ∧
      Function.Bijective Can := by
  have hR := rankAtStalk_eq hinj n hrank Can hCan hdim
  haveI : Module.Flat C A := flat_of_residue_rank hinj n hrank Can hCan hdim
  haveI : Module.FinitePresentation C A := Module.finitePresentation_of_rankAtStalk_eq A n hR
  haveI : Module.Projective C A := Module.Flat.projective_of_finitePresentation
  haveI : Module.Flat A B := inferInstance
  haveI : Module.Finite A (A ⊗[C] A) := inferInstance
  haveI : Module.Flat A (A ⊗[C] A) := inferInstance
  have hbij : Function.Bijective Can :=
    Module.bijective_of_surjective_of_rankAtStalk_eq (φ := Can.toLinearMap) hCan (fun p _ =>
      (Module.rankAtStalk_baseChange ⟨p, inferInstance⟩).trans
        ((hR _).trans (hrank ⟨p, inferInstance⟩).symm))
  have hff : Module.FaithfullyFlat C A := Module.FaithfullyFlat.of_comap_surjective
    ((PrimeSpectrum.comap_surjective_iff_injective_of_finite).mpr hinj)
  exact ⟨inferInstance, hff, hR, hbij⟩
end FourCorner.QuotientLocalFree
