import ThetaCoverClassPortable.CategoricalEqualizer
import ThetaCoverClassPortable.CofacesCoaction
import ThetaCoverClassPortable.InvertibleDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct CategoryTheory Algebra.DescentCofaces
open scoped ChangeOfRings

noncomputable section
universe u

namespace Module.FaithfullyFlat

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Effective faithfully flat descent using the genuine invariant equalizer.
The base-change equivalence respects the original two-pullback cocycle. -/
theorem exists_submodule_isBaseChange_of_cocycle [Module.FaithfullyFlat R S]
    (N : Type u) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (φ : (ModuleCat.extendScalars (i₁ R S).hom).obj (ModuleCat.of S N) ≅
      (ModuleCat.extendScalars (i₂ R S).hom).obj (ModuleCat.of S N))
    (hcoc : Cocycle (ModuleCat.of S N) φ.hom) :
    ∃ E : Submodule R N,
      Function.Injective E.subtype ∧ IsBaseChange S E.subtype ∧
      (∃ θ : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R E) ≅ ModuleCat.of S N,
        (∀ e : E, θ.hom ((1 : S) ⊗ₜ[R, algebraMap R S] e) = e.val) ∧
        (ModuleCat.extendScalars (i₁ R S).hom).map θ.hom ≫ φ.hom =
          canonical R S (ModuleCat.of R E) ≫ (ModuleCat.extendScalars (i₂ R S).hom).map θ.hom) ∧
      (Module.Invertible S N → Module.Invertible R E) := by
  let ρ := coactionOfIso R S N φ
  let E := coactionInvariants ρ
  have hcoassoc := coactionOfIso_coassoc_of_cocycle R S N φ hcoc
  have hE : IsBaseChange S E.subtype := isBaseChange_ofIso_of_coassoc R S N φ hcoassoc
  let θ := moduleIsoOfIsBaseChange R S hE
  refine ⟨E, Subtype.val_injective, hE, ⟨θ, ?_, ?_⟩, ?_⟩
  · intro e
    exact (moduleIsoOfIsBaseChange_tmul R S hE 1 e).trans (one_smul S e.val)
  · apply square_of_fixed_elements R S hE φ
    intro e
    exact (mem_coactionInvariants ρ e.val).mp e.property
  · intro hN
    letI := hN
    exact Module.Invertible.of_faithfullyFlat_of_isBaseChange hE

end Module.FaithfullyFlat
