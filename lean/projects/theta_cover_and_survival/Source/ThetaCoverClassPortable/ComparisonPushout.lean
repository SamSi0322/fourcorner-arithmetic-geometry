import ThetaCoverClassPortable.GlobalComparisonProjective
import Mathlib.Algebra.Category.Ring.Constructions
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace FourCorner.QuotientLocalFree
universe u
variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra A B]

/-- The right leg is retained as a distinct REAL ring map, not silently conflated
with the left A-action when both source rings have the same carrier type A. -/
def rightLeg (Can : A ⊗[C] A →ₐ[A] B) : A →+* B :=
  Can.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

theorem pushout_of_comparison_bijective (Can : A ⊗[C] A →ₐ[A] B)
    (hbij : Function.Bijective Can) :
    IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (rightLeg Can)) := by
  let e := (RingEquiv.ofBijective Can.toRingHom hbij).toCommRingCatIso
  refine (CommRingCat.isPushout_tensorProduct C A A).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) ?_ ?_
  · ext a
    exact Can.commutes a
  · rfl

/-- The global local-algebra leaf, INCLUDING the original two-leg pushout.
Every hypothesis is explicit generic data to be constructed by the actual quotient client. -/
theorem global_leaf [Module.Finite C A] [Module.Finite A B] [Module.Projective A B]
    (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n) :
    Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      (∀ p : PrimeSpectrum C, Module.rankAtStalk (R := C) A p = n) ∧
      Function.Bijective Can ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (rightLeg Can)) := by
  obtain ⟨hp, hff, hr, hbij⟩ := projective_ff_comparison hinj n hrank Can hCan hdim
  exact ⟨hp, hff, hr, hbij, pushout_of_comparison_bijective Can hbij⟩
end FourCorner.QuotientLocalFree
