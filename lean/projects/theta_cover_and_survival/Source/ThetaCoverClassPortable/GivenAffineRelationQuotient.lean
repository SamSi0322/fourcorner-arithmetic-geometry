import ThetaCoverClassPortable.InvariantSpecQuotientGeometry
import ThetaCoverClassPortable.AffineRelationTameInputs
import ThetaCoverClassPortable.TameFiniteRelationEffectivity
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.ActualAffineQuotient
open FourCorner.AffineRelationRank

/-- For the GIVEN original affine relation, ALL quotient algebra facts are
proved from its actual tame scheme inputs, then the canonical Spec/Gamma tail
constructs the genuine quotient. No effective quotient is a premise. -/
theorem given_affine_relation_invariant_projection_is_quotient
    {S X R : Scheme} [IsAffine S] [IsAffine X]
    (qS : S ⟶ Spec (.of ℚ)) (g : X ⟶ S) [LocallyOfFiniteType g]
    (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hst : s ≫ g = t ≫ g)
    (hmono : ∀ {T : Scheme} (a b : T ⟶ R),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme, Equivalence fun a b : T ⟶ X =>
      ∃ w : T ⟶ R, w ≫ s = a ∧ w ≫ t = b)
    (r : ℕ) (hrank : ∀ x : X, s.finrank x = r.factorial) :
    IsFinite (projection s t) ∧ Flat (projection s t) ∧
      LocallyOfFinitePresentation (projection s t) ∧ Surjective (projection s t) ∧
      IsPullback s t (projection s t) (projection s t) ∧
      Nonempty (IsColimit (Cofork.ofπ (projection s t)
        (by letI : IsAffine R := isAffine_of_isAffineHom s
            exact projection_coequalizes s t))) := by
  letI : IsAffine R := isAffine_of_isAffineHom s
  let qX := g ≫ qS
  have hq : s ≫ qX = t ≫ qX := common_rational_structure qS g s t hst
  letI := Scheme.TwoAffineOpenCover.algebraOfHom qX ⊤
  letI := invariantRationalAlgebra qX s t hq
  have hi := tame_inputs qS g s t hst hmono hequiv r hrank
  obtain ⟨_, hfinCA, hpositive, _, hfinB, hprojB, hrB⟩ := hi
  letI : Module.Finite (relationRing s t) Γ(X, ⊤) := hfinCA
  let sr := s.appTop.hom
  let tr := t.appTop.hom
  have htB : tr.Flat := HasRingHomProperty.appTop (P := @Flat) t inferInstance
  have hgen := FourCorner.FiniteRelationAffineInputs.range_sup_range_eq_top s t hmono
  have heq := FourCorner.FiniteRelationAffineInputs.equivalence_ringPoints s t hequiv
  have hinj : Function.Injective (algebraMap (relationRing s t) Γ(X, ⊤)) := Subtype.val_injective
  have hinv : ∀ a : Γ(X, ⊤), sr a = tr a ↔
      a ∈ Set.range (algebraMap (relationRing s t) Γ(X, ⊤)) := by
    intro a
    constructor
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact c.property
  have hbase : sr.comp (algebraMap ℚ Γ(X, ⊤)) = tr.comp (algebraMap ℚ Γ(X, ⊤)) :=
    common_rational_action qX s t hq
  obtain ⟨hfin, hproj, hff, hpo⟩ :=
    FourCorner.FiniteRelationQuotient.tame_finite_relation_quotient
      sr tr hfinB hprojB htB hgen heq hinj hinv hbase r.factorial
      (Nat.ne_of_gt hpositive) hrB
  letI : Module.Finite (relationRing s t) Γ(X, ⊤) := hfin
  letI : Module.Projective (relationRing s t) Γ(X, ⊤) := hproj
  letI : Module.FaithfullyFlat (relationRing s t) Γ(X, ⊤) := hff
  exact projection_is_quotient_of_algebra_data s t hpo

/-- Given-relation existential packaging. The quotient is exactly Spec of
the same literal eqLocus, and no new R,s,t witness is chosen. -/
theorem given_affine_relation_quotient
    {S X R : Scheme} [IsAffine S] [IsAffine X]
    (qS : S ⟶ Spec (.of ℚ)) (g : X ⟶ S) [LocallyOfFiniteType g]
    (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hst : s ≫ g = t ≫ g)
    (hmono : ∀ {T : Scheme} (a b : T ⟶ R),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme, Equivalence fun a b : T ⟶ X =>
      ∃ w : T ⟶ R, w ≫ s = a ∧ w ≫ t = b)
    (r : ℕ) (hrank : ∀ x : X, s.finrank x = r.factorial) :
    ∃ (Y : Scheme) (_ : IsAffine Y) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  letI : IsAffine R := isAffine_of_isAffineHom s
  obtain ⟨hfin, hf, hfp, hs, hpb, hc⟩ :=
    given_affine_relation_invariant_projection_is_quotient qS g s t hst hmono hequiv r hrank
  exact ⟨Spec (.of (relationRing s t)), inferInstance, projection s t,
    projection_coequalizes s t, hfin, hf, hfp, hs, hpb, hc⟩

end FourCorner.ActualAffineQuotient
