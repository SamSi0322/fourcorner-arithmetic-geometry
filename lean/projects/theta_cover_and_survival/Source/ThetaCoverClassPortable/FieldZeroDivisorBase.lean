import ThetaCoverClassPortable.FieldZeroDivisor
import ThetaCoverClassPortable.FiniteMapDataBaseChange
import Mathlib.AlgebraicGeometry.Geometrically.Integral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra
namespace FourCorner.FieldZeroDivisor

/-- Honest actual-finite-map variant: the datum on the field fibre and its integrality
are constructed internally. The field, section and two-affine cover are arbitrary. -/
theorem exists_zero_divisor_over_field_of_finiteMapData
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (F : SmoothProperCurve.FiniteMapData c ε)
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    {M : (pullback c x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback c x).Modules ⟶ M) (hs : s ≠ 0)
    (V : (pullback c x).TwoAffineOpenCover) (d : ℕ)
    (hχ : (Module.finrank k (V.sectionsOf (pullback.snd c x) M).H0 : ℤ)
        - Module.finrank k (V.sectionsOf (pullback.snd c x) M).H1
      = (Module.finrank k (V.sectionsOf (pullback.snd c x) (𝟙_ (pullback c x).Modules)).H0 : ℤ)
        - Module.finrank k (V.sectionsOf (pullback.snd c x) (𝟙_ (pullback c x).Modules)).H1 + d) :
    ∃ D : RelEffCartierDiv c d x, D.I = Scheme.Modules.zeroSchemeIdeal s ∧
      ∃ e : M ≅ D.lineBundle, s ≫ e.hom = D.I.invModuleSection := by
  obtain ⟨a,ha⟩ := Spec.map_surjective x
  letI : Algebra R k := a.hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k = x := ha
  subst x
  letI : IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap R k)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := c)
      (Scheme.TwoAffineOpenCover.specMap R k) (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _)
  exact exists_zero_divisor_of_finiteMapData (Scheme.TwoAffineOpenCover.specMap R k)
    (F.baseChange k) hM s hs V d hχ
end FourCorner.FieldZeroDivisor
