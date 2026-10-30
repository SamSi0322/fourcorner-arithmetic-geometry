import ThetaCoverClassPortable.InvertibleDescent
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalRing.Module

set_option autoImplicit false

open TensorProduct LinearMap
noncomputable section

namespace Module

universe u v
variable {A : Type u} [CommRing A]

/-- Bijectivity is detected by actual tensor localizations at maximal ideals. -/
theorem bijective_of_baseChange_atMaximal {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N)
    (h : ∀ (P : Ideal A) [P.IsMaximal],
      Function.Bijective (f.baseChange (Localization.AtPrime P))) : Function.Bijective f := by
  apply bijective_of_isLocalized_maximal
    (fun P _ => Localization.AtPrime P ⊗[A] M)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) M 1)
    (fun P _ => Localization.AtPrime P ⊗[A] N)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) N 1) f
  intro P hP
  have he : IsLocalizedModule.map P.primeCompl
      (TensorProduct.mk A (Localization.AtPrime P) M 1)
      (TensorProduct.mk A (Localization.AtPrime P) N 1) f =
        (f.baseChange (Localization.AtPrime P)).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl
      (TensorProduct.mk A (Localization.AtPrime P) M 1)
      (TensorProduct.mk A (Localization.AtPrime P) N 1)
    ext m
    simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.baseChange_tmul, TensorProduct.mk_apply] using
      IsLocalizedModule.map_apply P.primeCompl
        (TensorProduct.mk A (Localization.AtPrime P) M 1)
        (TensorProduct.mk A (Localization.AtPrime P) N 1) f m
  rw [he]
  exact h P

/-- The actual dual evaluation map becomes an isomorphism whenever a finite
projective module has invertible base change. -/
theorem contractLeft_baseChange_bijective (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Projective A M]
    (S : Type*) [CommRing S] [Algebra A S] [Module.Invertible S (S ⊗[A] M)] :
    Function.Bijective ((contractLeft A M).baseChange S) := by
  let e : S ⊗[A] (Dual A M ⊗[A] M) ≃ₗ[S] S :=
    AlgebraTensorModule.distribBaseChange A S (Dual A M) M ≪≫ₗ
      (finiteProjectiveDualBaseChange (R := A) (S := S) (M := M)).rTensor (S ⊗[A] M) ≪≫ₗ
        Invertible.linearEquiv S (S ⊗[A] M)
  have he : (AlgebraTensorModule.rid A S S).toLinearMap ∘ₗ
      (contractLeft A M).baseChange S = e.toLinearMap := by
    ext s f m
    simp [e, Invertible.linearEquiv, Algebra.smul_def, mul_comm]
  have hh : (contractLeft A M).baseChange S =
      (AlgebraTensorModule.rid A S S).symm.toLinearMap ∘ₗ e.toLinearMap := by
    rw [← he]
    ext x
    simp
  rw [hh]
  exact (AlgebraTensorModule.rid A S S).symm.bijective.comp e.bijective

/-- A finite projective module with one-dimensional fibres over every field
is genuinely invertible, over an arbitrary commutative base ring. -/
theorem Invertible.of_projective_of_forall_finrank_eq_one
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] [Projective A M]
    (hrank : ∀ (K : Type u) [Field K] [Algebra A K], finrank K (K ⊗[A] M) = 1) :
    Module.Invertible A M := by
  refine ⟨bijective_of_baseChange_atMaximal (contractLeft A M) ?_⟩
  intro P hP
  let S := Localization.AtPrime P
  have hlocal : ∀ Q : MaximalSpectrum S,
      finrank (S ⧸ Q.1) ((S ⧸ Q.1) ⊗[S] (S ⊗[A] M)) = 1 := by
    intro Q
    let K := S ⧸ Q.1
    letI : Field K := Ideal.Quotient.field Q.1
    exact (AlgebraTensorModule.cancelBaseChange A S K K M).finrank_eq.trans (hrank K)
  obtain ⟨b⟩ := nonempty_basis_of_flat_of_finrank_eq S (S ⊗[A] M) 1 hlocal
  let e : (S ⊗[A] M) ≃ₗ[S] S := b.repr ≪≫ₗ Finsupp.uniqueLinearEquiv S S (0 : Fin 1)
  letI : Module.Invertible S (S ⊗[A] M) := Invertible.congr e.symm
  exact contractLeft_baseChange_bijective M S

end Module
