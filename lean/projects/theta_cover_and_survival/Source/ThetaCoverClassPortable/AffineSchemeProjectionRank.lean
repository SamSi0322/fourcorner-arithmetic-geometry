import ThetaCoverClassPortable.FiniteRelationAffineFiniteness
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace FourCorner.AffineRelationRank

/-- The EXACT s.appTop action has the scheme's native degree at EVERY prime.
The comparison uses the actual affine Spec-Gamma square, not field samples. -/
theorem rankAtStalk_eq_scheme_finrank {X R : Scheme.{u}} [IsAffine X]
    (s : R ⟶ X) [IsFinite s] [Flat s] (p : PrimeSpectrum Γ(X, ⊤)) :
    letI := s.appTop.hom.toAlgebra
    Module.rankAtStalk (R := Γ(X, ⊤)) Γ(R, ⊤) p =
      s.finrank (X.isoSpec.inv p) := by
  letI : IsAffine R := isAffine_of_isAffineHom s
  letI := s.appTop.hom.toAlgebra
  have hfinite := s.finite_appTop
  have hflat : s.appTop.hom.Flat := HasRingHomProperty.appTop (P := @Flat) s inferInstance
  have hnat : R.isoSpec.inv ≫ s = Spec.map s.appTop ≫ X.isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact (Scheme.isoSpec_hom_naturality s).symm
  have hsq : IsPullback R.isoSpec.inv (Spec.map s.appTop) s X.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨hnat⟩
  calc
    Module.rankAtStalk (R := Γ(X, ⊤)) Γ(R, ⊤) p = s.appTop.hom.finrank p := rfl
    _ = (Spec.map s.appTop).finrank p :=
      congrFun (Scheme.Hom.finrank_SpecMap_eq_finrank hfinite hflat).symm p
    _ = s.finrank (X.isoSpec.inv p) :=
      Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq p

/-- The scheme's actual constant degree gives constant module rank for the
SAME global-section map and the SAME module; no freeness is assumed. -/
theorem rankAtStalk_eq_const {X R : Scheme.{u}} [IsAffine X]
    (s : R ⟶ X) [IsFinite s] [Flat s] (n : ℕ)
    (hs : ∀ x : X, s.finrank x = n) :
    letI := s.appTop.hom.toAlgebra
    ∀ p : PrimeSpectrum Γ(X, ⊤), Module.rankAtStalk (R := Γ(X, ⊤)) Γ(R, ⊤) p = n := by
  intro p
  exact (rankAtStalk_eq_scheme_finrank s p).trans (hs _)

end FourCorner.AffineRelationRank
