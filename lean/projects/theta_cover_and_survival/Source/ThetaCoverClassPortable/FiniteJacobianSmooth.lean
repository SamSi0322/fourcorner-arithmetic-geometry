import ThetaCoverClassPortable.geometry.SchemeModelFiniteExtension
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

noncomputable section
namespace FourCorner.FiniteJacobianSmooth
open Algebra
universe u v w t
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]

/-- Localizing a genuine finite polynomial presentation at its actual selected Jacobian
minor produces a submersive presentation, without assuming smoothness. -/
def localizationSubmersive (P : PreSubmersivePresentation R S ι σ) :
    SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) where
  toPreSubmersivePresentation :=
    (PreSubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian).comp P
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact IsUnit.mul (IsLocalization.Away.algebraMap_isUnit P.jacobian)
      (IsLocalization.Away.algebraMap_isUnit P.jacobian)

/-- The local Jacobian chart has exactly the dimension generators minus relations. -/
theorem localization_standardSmooth (P : PreSubmersivePresentation R S ι σ) :
    IsStandardSmoothOfRelativeDimension P.dimension R (Localization.Away P.jacobian) := by
  apply (localizationSubmersive P).isStandardSmoothOfRelativeDimension
  simp only [localizationSubmersive, PreSubmersivePresentation.toPresentation_comp,
    Presentation.dimension, Nat.card_sum, Nat.card_unique, Nat.add_sub_add_left]

section SameUniverse
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {V E κ : Type*} [Finite V] [Finite E]

/-- A covering family of actual Jacobian minors gives local standard smoothness. -/
theorem locally_of_jacobian_span (P : κ → PreSubmersivePresentation A B V E)
    (hspan : Ideal.span (Set.range (fun i => (P i).jacobian)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Nat.card V - Nat.card E))
      (algebraMap A B) := by
  refine ⟨Set.range (fun i => (P i).jacobian), hspan, ?_⟩
  rintro _ ⟨i,rfl⟩
  rw [← IsScalarTower.algebraMap_eq A B (Localization.Away (P i).jacobian),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact localization_standardSmooth (P i)

/-- The same criterion is a property of the genuine affine scheme morphism. -/
theorem spec_smooth_of_jacobian_span (P : κ → PreSubmersivePresentation A B V E)
    (hspan : Ideal.span (Set.range (fun i => (P i).jacobian)) = ⊤) :
    AlgebraicGeometry.SmoothOfRelativeDimension (Nat.card V - Nat.card E)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension (Nat.card V - Nat.card E))).mpr
  exact locally_of_jacobian_span P hspan


/-- Nonvanishing of some selected Jacobian at every field-valued point forces the minors
to generate the unit ideal; the residue field of an actual maximal ideal detects failure. -/
theorem jacobian_span_of_field_points {K : Type u} [Field K] [Algebra K B]
    (P : κ → PreSubmersivePresentation K B V E)
    (h : ∀ (F : Type u) [Field F] [Algebra K F] (f : B →ₐ[K] F),
      ∃ i, f (P i).jacobian ≠ 0) :
    Ideal.span (Set.range (fun i => (P i).jacobian)) = ⊤ := by
  by_contra hn
  obtain ⟨M,hM,hsub⟩ := Ideal.exists_le_maximal _ hn
  letI : M.IsMaximal := hM
  letI : Field (B ⧸ M) := Ideal.Quotient.field M
  obtain ⟨i,hi⟩ := h (B ⧸ M) (Ideal.Quotient.mkₐ K M)
  apply hi
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hsub (Ideal.subset_span ⟨i,rfl⟩))

end SameUniverse

end FourCorner.FiniteJacobianSmooth
#print axioms FourCorner.FiniteJacobianSmooth.localizationSubmersive
#print axioms FourCorner.FiniteJacobianSmooth.localization_standardSmooth

#print axioms FourCorner.FiniteJacobianSmooth.locally_of_jacobian_span
#print axioms FourCorner.FiniteJacobianSmooth.spec_smooth_of_jacobian_span

#print axioms FourCorner.FiniteJacobianSmooth.jacobian_span_of_field_points
