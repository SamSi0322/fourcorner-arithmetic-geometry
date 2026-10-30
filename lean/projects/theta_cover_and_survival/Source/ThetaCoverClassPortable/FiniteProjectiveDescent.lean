import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.EquationalCriterion

set_option autoImplicit false
open TensorProduct
noncomputable section

namespace Module
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [FaithfullyFlat R S]

/-- Finite presentation descends along genuine faithfully flat scalar extension. -/
theorem FinitePresentation.of_faithfullyFlat_tensorProduct
    [FinitePresentation S (S ⊗[R] M)] : FinitePresentation R M := by
  letI : Module.Finite R M := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let k := (LinearMap.ker f).subtype.baseChange S
  have hex : Function.Exact k (f.baseChange S) := Flat.lTensor_exact S f.exact_subtype_ker_map
  have hker : LinearMap.range k = LinearMap.ker (f.baseChange S) :=
    (LinearMap.exact_iff.mp hex).symm
  have hfg := FinitePresentation.fg_ker (f.baseChange S) (LinearMap.lTensor_surjective S hf)
  letI : Module.Finite S (LinearMap.range k) := Module.Finite.of_fg (hker.symm ▸ hfg)
  have hinj : Function.Injective k :=
    Flat.lTensor_preserves_injective_linearMap (LinearMap.ker f).subtype (Submodule.injective_subtype _)
  letI : Module.Finite S (S ⊗[R] LinearMap.ker f) := Module.Finite.equiv (LinearEquiv.ofInjective k hinj).symm
  letI : Module.Finite R (LinearMap.ker f) := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  exact finitePresentation_of_free_of_surjective f hf (Module.Finite.iff_fg.mp inferInstance)

/-- Projectivity descends with finite presentation along a faithfully flat algebra. -/
theorem Projective.of_faithfullyFlat_tensorProduct
    [Module.Finite S (S ⊗[R] M)] [Projective S (S ⊗[R] M)] :
    Projective R M := by
  letI : FinitePresentation S (S ⊗[R] M) := finitePresentation_of_projective _ _
  letI : FinitePresentation R M := FinitePresentation.of_faithfullyFlat_tensorProduct (S := S)
  letI : Flat R M := Flat.of_flat_tensorProduct R M S
  exact Flat.projective_of_finitePresentation
end Module
