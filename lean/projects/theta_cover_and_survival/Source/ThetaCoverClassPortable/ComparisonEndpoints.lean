import ThetaCoverClassPortable.ComparisonPushout
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace FourCorner.QuotientLocalFree
universe u
variable {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra A B] [Module.Finite C A]
  [Module.Finite A B] [Module.Projective A B]

def comparisonEquiv (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n) :
    A ⊗[C] A ≃ₐ[A] B :=
  AlgEquiv.ofBijective Can (projective_ff_comparison hinj n hrank Can hCan hdim).2.2.2

@[simp] theorem comparisonEquiv_apply (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n)
    (x : A ⊗[C] A) : comparisonEquiv hinj n hrank Can hCan hdim x = Can x := rfl

omit [Module.Finite C A] [Module.Finite A B] [Module.Projective A B] in
/-- Transfer to a caller's existing right leg by its actual pure-tensor formula. -/
theorem rightLeg_eq (Can : A ⊗[C] A →ₐ[A] B) (t : A →+* B)
    (hright : ∀ a : A, Can ((1 : A) ⊗ₜ[C] a) = t a) : rightLeg Can = t :=
  RingHom.ext hright

/-- Rank zero is not silently discarded: all global hypotheses with n=0 force
C itself to be the zero ring. The global theorem allows that case. -/
theorem zero_rank_forces_subsingleton (hinj : Function.Injective (algebraMap C A))
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = 0)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = 0) :
    Subsingleton C := by
  obtain ⟨hp, _, hR, _⟩ := projective_ff_comparison hinj 0 hrank Can hCan hdim
  haveI : Module.Projective C A := hp
  haveI : Module.Flat C A := inferInstance
  have hz : Module.rankAtStalk (R := C) A = 0 := funext hR
  haveI : Subsingleton A := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hz
  exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩

/-- The actual caller may retain its pre-existing t; the generic geometric pushout
uses the original distinct legs s and t, not a conflated A-algebra structure. -/
theorem global_leaf_for_right_leg (hinj : Function.Injective (algebraMap C A)) (n : ℕ)
    (hrank : ∀ q : PrimeSpectrum A, Module.rankAtStalk (R := A) B q = n)
    (Can : A ⊗[C] A →ₐ[A] B) (hCan : Function.Surjective Can)
    (hdim : ∀ p : PrimeSpectrum C,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[C] A) = n)
    (t : A →+* B) (hright : ∀ a : A, Can ((1 : A) ⊗ₜ[C] a) = t a) :
    Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      (∀ p : PrimeSpectrum C, Module.rankAtStalk (R := C) A p = n) ∧
      Function.Bijective Can ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom t) := by
  obtain ⟨hp, hff, hR, hb, hpo⟩ := global_leaf hinj n hrank Can hCan hdim
  exact ⟨hp, hff, hR, hb, by simpa only [rightLeg_eq Can t hright] using hpo⟩
end FourCorner.QuotientLocalFree
