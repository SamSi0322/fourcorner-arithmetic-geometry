import ThetaCoverClassPortable.FiniteRelationStructure
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Tactic.Algebraize
import Mathlib.RingTheory.Flat.EquationalCriterion
import ThetaCoverClassPortable.ThetaStdModuleFinitePresentation

/-! Exact three prerequisite proof bodies from the fully read original
Scheme quotient caller (SHA 91d680dd922b8e25fc01b46d851c7789ee7308d2afaec4a69d5a12dc0a9fafea).
Imports/namespace are changed; two ambiguous finite-appTop lookups use the exact pinned Scheme.Hom.finite_appTop API. The missing quotient leaf is neither
imported nor used. All scheme tests and nilpotent tests are retained. -/
namespace FourCorner.FiniteRelationAffineInputs
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
theorem finite_projective_appTop {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s] :
    (letI := s.appTop.hom.toAlgebra; Module.Finite Γ(X, ⊤) Γ(R, ⊤)) ∧
    (letI := s.appTop.hom.toAlgebra; Module.Projective Γ(X, ⊤) Γ(R, ⊤)) := by
  have h₁ : RingHom.Finite s.appTop.hom :=
    s.finite_appTop
  have h₂ : RingHom.Flat s.appTop.hom := HasRingHomProperty.appTop (P := @Flat) s inferInstance
  have h₃ : RingHom.FinitePresentation s.appTop.hom :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) s inferInstance
  algebraize [s.appTop.hom]
  refine ⟨h₁, ?_⟩
  have : Module.FinitePresentation Γ(X, ⊤) Γ(R, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  exact Module.Flat.projective_of_finitePresentation

theorem range_sup_range_eq_top {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s t : R ⟶ X)
    [IsFinite s]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b) :
    s.appTop.hom.range ⊔ t.appTop.hom.range = ⊤ := by
  classical
  set B₀ : Subring Γ(R, ⊤) := s.appTop.hom.range ⊔ t.appTop.hom.range with hB₀

  let s₀ : Γ(X, ⊤) →+* B₀ := s.appTop.hom.codRestrict B₀ (fun a => by
    rw [hB₀]; exact (le_sup_left : s.appTop.hom.range ≤ _) ⟨a, rfl⟩)
  let t₀ : Γ(X, ⊤) →+* B₀ := t.appTop.hom.codRestrict B₀ (fun a => by
    rw [hB₀]; exact (le_sup_right : t.appTop.hom.range ≤ _) ⟨a, rfl⟩)

  let incl : CommRingCat.of B₀ ⟶ Γ(R, ⊤) := CommRingCat.ofHom B₀.subtype
  have hfacs : s.appTop = CommRingCat.ofHom s₀ ≫ incl := by ext; rfl
  have hfact : t.appTop = CommRingCat.ofHom t₀ ≫ incl := by ext; rfl
  have hnat : ∀ f : R ⟶ X, R.isoSpec.inv ≫ f = Spec.map f.appTop ≫ X.isoSpec.inv := fun f => by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (Scheme.isoSpec_hom_naturality f).symm
  haveI : Epi incl := by
    constructor
    intro T φ ψ h
    have key : Spec.map φ ≫ R.isoSpec.inv = Spec.map ψ ≫ R.isoSpec.inv := by
      apply hmono
      · simp only [Category.assoc, hnat, ← Spec.map_comp_assoc]
        rw [hfacs, Category.assoc, Category.assoc, h]
      · simp only [Category.assoc, hnat, ← Spec.map_comp_assoc]
        rw [hfact, Category.assoc, Category.assoc, h]
    have : Spec.map φ = Spec.map ψ := by
      simpa using congrArg (· ≫ R.isoSpec.hom) key
    exact Spec.map_injective this

  have hfin : RingHom.Finite incl.hom := by
    have h₁ : RingHom.Finite s.appTop.hom :=
      s.finite_appTop
    have hfac : incl.hom.comp s₀ = s.appTop.hom := RingHom.ext fun _ => rfl
    rw [← hfac] at h₁
    exact RingHom.Finite.of_comp_finite h₁
  have hsurj : Function.Surjective incl.hom := RingHom.surjective_of_epi_of_finite incl hfin
  rw [eq_top_iff]
  rintro b -
  obtain ⟨⟨b₀, hb₀⟩, rfl⟩ := hsurj b
  exact hb₀

theorem equivalence_ringPoints {X R : Scheme.{u}} [IsAffine X] [IsAffine R] (s t : R ⟶ X)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (T : Type u) [CommRing T] :
    _root_.Equivalence fun x y : Γ(X, ⊤) →+* T =>
      ∃ φ : Γ(R, ⊤) →+* T, φ.comp s.appTop.hom = x ∧ φ.comp t.appTop.hom = y := by

  let Φ : (Γ(X, ⊤) →+* T) → (Spec (.of T) ⟶ X) := fun x =>
    Spec.map (CommRingCat.ofHom x) ≫ X.isoSpec.inv
  let ΦR : (Γ(R, ⊤) →+* T) → (Spec (.of T) ⟶ R) := fun φ =>
    Spec.map (CommRingCat.ofHom φ) ≫ R.isoSpec.inv
  have hnat : ∀ f : R ⟶ X, R.isoSpec.inv ≫ f = Spec.map f.appTop ≫ X.isoSpec.inv := fun f => by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (Scheme.isoSpec_hom_naturality f).symm
  have hΦ : ∀ (f : R ⟶ X) (φ : Γ(R, ⊤) →+* T), ΦR φ ≫ f = Φ (φ.comp f.appTop.hom) := fun f φ => by
    simp only [ΦR, Φ, Category.assoc, hnat, ← Spec.map_comp_assoc, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom]
  have hsurjR : ∀ ψ : Spec (.of T) ⟶ R, ∃ φ, ΦR φ = ψ := fun ψ => by
    obtain ⟨g, hg⟩ := Spec.map_surjective (ψ ≫ R.isoSpec.hom)
    refine ⟨g.hom, ?_⟩
    simp only [ΦR, CommRingCat.ofHom_hom, hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hΦinj : Function.Injective Φ := fun x y hxy => by
    have h1 : Spec.map (CommRingCat.ofHom x) = Spec.map (CommRingCat.ofHom y) := by
      simpa [Φ] using congrArg (· ≫ X.isoSpec.hom) hxy
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have key : ∀ x y : Γ(X, ⊤) →+* T,
      (∃ φ : Γ(R, ⊤) →+* T, φ.comp s.appTop.hom = x ∧ φ.comp t.appTop.hom = y) ↔
        (∃ ψ : Spec (.of T) ⟶ R, ψ ≫ s = Φ x ∧ ψ ≫ t = Φ y) := fun x y => by
    constructor
    · rintro ⟨φ, rfl, rfl⟩
      exact ⟨ΦR φ, hΦ s φ, hΦ t φ⟩
    · rintro ⟨ψ, h1, h2⟩
      obtain ⟨φ, rfl⟩ := hsurjR ψ
      exact ⟨φ, hΦinj (by rw [← hΦ, h1]), hΦinj (by rw [← hΦ, h2])⟩
  have E := hequiv (Spec (.of T))
  exact
    { refl := fun x => (key x x).2 (E.refl _)
      symm := fun h => (key _ _).2 (E.symm ((key _ _).1 h))
      trans := fun h h' => (key _ _).2 (E.trans ((key _ _).1 h) ((key _ _).1 h')) }

#print axioms finite_projective_appTop
#print axioms range_sup_range_eq_top
#print axioms equivalence_ringPoints
end FourCorner.FiniteRelationAffineInputs
