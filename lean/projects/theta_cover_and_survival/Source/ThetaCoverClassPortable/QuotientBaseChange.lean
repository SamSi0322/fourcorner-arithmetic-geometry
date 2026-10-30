import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace FourCorner.FiniteLocallyFreeQuotient
/-- Base change of the ACTUAL original kernel pair. Both given squares and
both actual leg compatibilities are retained; no new effectivity is assumed. -/
theorem kernelPair_baseChange {Cat : Type*} [Category Cat]
    {R X Y R' X' Y' : Cat} {s t : R ⟶ X} {p : X ⟶ Y}
    {r : R' ⟶ R} {x : X' ⟶ X} {y : Y' ⟶ Y}
    {s' t' : R' ⟶ X'} {p' : X' ⟶ Y'}
    (hR : IsPullback s t p p) (hX : IsPullback x p' p y)
    (hsq : IsPullback r s' s x) (htq : r ≫ t=t' ≫ x)
    (w' : s' ≫ p'=t' ≫ p') : IsPullback s' t' p' p' := by
  have outer := hsq.paste_horiz hR.flip
  rw [htq,hX.w] at outer
  exact (outer.of_right w'.symm hX).flip
end FourCorner.FiniteLocallyFreeQuotient

namespace AlgebraicGeometry.Scheme
/-- The genuine finite locally free quotient package is stable under the
specified actual base-change squares. Coequalizer effectivity follows from
the proved native fpqc effective-epimorphism theorem. -/
theorem quotient_baseChange_of_finiteLocallyFree_of_isPullback
    {R X Y R' X' Y' : Scheme.{u}} {s t : R ⟶ X} {p : X ⟶ Y}
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    {r : R' ⟶ R} {x : X' ⟶ X} {y : Y' ⟶ Y}
    {s' t' : R' ⟶ X'} {p' : X' ⟶ Y'}
    (hR : IsPullback s t p p) (hX : IsPullback x p' p y)
    (hsq : IsPullback r s' s x) (htq : r ≫ t=t' ≫ x)
    (w' : s' ≫ p'=t' ≫ p') :
    IsFinite p' ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' ∧
      IsPullback s' t' p' p' ∧ Nonempty (IsColimit (Cofork.ofπ p' w')) := by
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P:=@IsFinite) hX inferInstance
  haveI : Flat p' := MorphismProperty.of_isPullback (P:=@Flat) hX inferInstance
  haveI : LocallyOfFinitePresentation p' :=
    MorphismProperty.of_isPullback (P:=@LocallyOfFinitePresentation) hX inferInstance
  haveI : Surjective p' := MorphismProperty.of_isPullback (P:=@Surjective) hX inferInstance
  have hp := FourCorner.FiniteLocallyFreeQuotient.kernelPair_baseChange hR hX hsq htq w'
  have hk : IsKernelPair p' s' t' := hp
  exact ⟨inferInstance,inferInstance,inferInstance,inferInstance,hp,
    ⟨hk.toCoequalizer (regularEpiOfEffectiveEpi p')⟩⟩
end AlgebraicGeometry.Scheme
