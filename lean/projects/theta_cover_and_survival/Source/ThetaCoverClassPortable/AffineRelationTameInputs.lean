import ThetaCoverClassPortable.AffineRelationRationalScalars
import ThetaCoverClassPortable.SameDivisorRelationInputs

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FourCorner.AffineRelationRank

theorem common_rational_structure {S X R : Scheme} (qS : S ⟶ Spec (.of ℚ))
    (g : X ⟶ S) (s t : R ⟶ X) (hst : s ≫ g = t ≫ g) :
    s ≫ (g ≫ qS) = t ≫ (g ≫ qS) := by
  simpa only [Category.assoc] using congrArg (· ≫ qS) hst

/-- This is only the requested actual tame INPUT conjunction. It contains no
quotient, C-flatness, free-module, comparison-injectivity or effectivity field. -/
def TameInputs {S X R : Scheme} (qS : S ⟶ Spec (.of ℚ)) (g : X ⟶ S)
    (s t : R ⟶ X) (hst : s ≫ g = t ≫ g) (r : ℕ) : Prop :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (g ≫ qS) ⊤
  letI := invariantRationalAlgebra (g ≫ qS) s t (common_rational_structure qS g s t hst)
  IsScalarTower ℚ (invariantRing s t) Γ(X, ⊤) ∧
  Module.Finite (invariantRing s t) Γ(X, ⊤) ∧
  0 < r.factorial ∧ IsUnit (r.factorial : invariantRing s t) ∧
  (letI := s.appTop.hom.toAlgebra
   Module.Finite Γ(X, ⊤) Γ(R, ⊤) ∧ Module.Projective Γ(X, ⊤) Γ(R, ⊤) ∧
   ∀ p : PrimeSpectrum Γ(X, ⊤), Module.rankAtStalk (R := Γ(X, ⊤)) Γ(R, ⊤) p = r.factorial)

/-- Actual affine scheme hypotheses and native constant degree internally
supply every tame scalar/rank/unit input, with the SAME exact eqLocus C. -/
theorem tame_inputs {S X R : Scheme} [IsAffine S] [IsAffine X]
    (qS : S ⟶ Spec (.of ℚ)) (g : X ⟶ S) [LocallyOfFiniteType g]
    (s t : R ⟶ X) [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    (hst : s ≫ g = t ≫ g)
    (hmono : ∀ {T : Scheme} (a b : T ⟶ R),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme, Equivalence fun x y : T ⟶ X =>
      ∃ w : T ⟶ R, w ≫ s = x ∧ w ≫ t = y)
    (r : ℕ) (hrank : ∀ x : X, s.finrank x = r.factorial) :
    TameInputs qS g s t hst r := by
  letI : IsAffine R := isAffine_of_isAffineHom s
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (g ≫ qS) ⊤
  letI := invariantRationalAlgebra (g ≫ qS) s t (common_rational_structure qS g s t hst)
  obtain ⟨hf, hp⟩ := FourCorner.FiniteRelationAffineInputs.finite_projective_appTop s
  exact ⟨invariantRationalTower _ _ _ _,
    FourCorner.FiniteRelationAffineFiniteness.finite_invariant_globalSections g s t hst hmono hequiv,
    Nat.factorial_pos r, positive_nat_isUnit _ _ (Nat.factorial_pos r),
    hf, hp, rankAtStalk_eq_const s r.factorial hrank⟩

end FourCorner.AffineRelationRank
