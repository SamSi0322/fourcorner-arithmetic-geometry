import ThetaCoverClassPortable.ReplayImports
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.LocalProperties.FinitePresentation
set_option autoImplicit false
noncomputable section
namespace Module
variable {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Flat R M]

/-- The actual caller has BOTH finite generation and flatness. Constant stalk rank
then supplies genuine local bases and descends a finite presentation. -/
theorem finitePresentation_of_rankAtStalk_eq (n : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n) :
    Module.FinitePresentation R M := by
  classical
  let s : Set R := {a | Module.Free (Localization.Away a) (LocalizedModule.Away a M)}
  have hspan : Ideal.span s = ⊤ := by
    by_contra hn
    obtain ⟨p, hpm, hple⟩ := (Ideal.span s).exists_le_maximal hn
    letI := hpm
    obtain ⟨a, hap, ha⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M p
      (fun q _ => (h ⟨q, inferInstance⟩).trans (h ⟨p, inferInstance⟩).symm)
    exact hap (hple (Ideal.subset_span ha))
  apply Module.FinitePresentation.of_localizationSpan s hspan
  intro a
  haveI : Module.Free (Localization.Away a.1) (LocalizedModule.Away a.1 M) := a.2
  exact Module.finitePresentation_of_projective _ _
end Module
