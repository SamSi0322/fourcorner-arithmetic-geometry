import ThetaCoverClassPortable.IteratedBaseChangeIso
import ThetaCoverClassPortable.ThetaUniversalGlobalSections

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.IteratedStructuralBaseChange

namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels

/-- Actual canonical comparison (C_R)_S ≅ C_S. The Q-algebra on S is
explicitly the composite Q -> R -> S; no external tower is required. -/
def actual_iterated_baseChange_iso (R S : Type) [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra R S] :
    letI := composedAlgebra ℚ R S
    pullback (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ R))
      (Scheme.TwoAffineOpenCover.specMap R S) ≅
    pullback (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ S) :=
  baseChangeIsoViaComposite (cToBase ℚ)

/-- The actual canonical comparison preserves the base-S map. -/
theorem actual_iterated_baseChange_iso_over (R S : Type) [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra R S] :
    letI := composedAlgebra ℚ R S
    (actual_iterated_baseChange_iso R S).hom ≫
        pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ S) =
      pullback.snd (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ R))
        (Scheme.TwoAffineOpenCover.specMap R S) := by
  letI := composedAlgebra ℚ R S
  letI : IsScalarTower ℚ R S := composedTower ℚ R S
  exact baseChangeIso_over (cToBase ℚ)

/-- Actual comparison of global functions as S-ALGEBRAS, not just modules. -/
def actual_iterated_sections_algEquiv (R S : Type) [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra R S] :
    letI := composedAlgebra ℚ R S
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ S)) ⊤
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ R))
        (Scheme.TwoAffineOpenCover.specMap R S)) ⊤
    Γ(pullback (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ S), ⊤) ≃ₐ[S]
      Γ(pullback (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ R))
        (Scheme.TwoAffineOpenCover.specMap R S), ⊤) := by
  letI := composedAlgebra ℚ R S
  letI : IsScalarTower ℚ R S := composedTower ℚ R S
  exact sectionsAlgEquiv (cToBase ℚ)

/-- For EVERY Q-algebra R and EVERY commutative R-algebra S, including
zero rings, the structural S -> Γ((C_R)_S, top) is bijective. -/
theorem actual_iterated_universal_global_sections (R S : Type) [CommRing R] [Algebra ℚ R]
    [CommRing S] [Algebra R S] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (pullback.snd (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ R))
        (Scheme.TwoAffineOpenCover.specMap R S)) ⊤
    Function.Bijective (algebraMap S
      Γ(pullback (pullback.snd (cToBase ℚ) (Scheme.TwoAffineOpenCover.specMap ℚ R))
        (Scheme.TwoAffineOpenCover.specMap R S), ⊤)) := by
  letI := composedAlgebra ℚ R S
  letI : IsScalarTower ℚ R S := composedTower ℚ R S
  exact bijective_algebraMap_iterated (R := R) (cToBase ℚ)
    (actual_universal_global_sections S)

end FourCorner.ThetaRationalPicardInput
