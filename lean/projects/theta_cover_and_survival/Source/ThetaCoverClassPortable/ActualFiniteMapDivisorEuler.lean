import ThetaCoverClassPortable.FieldZeroEuler
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ThetaCoverClassPortable.FiniteMapDataBaseChange

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
universe u
namespace FourCorner.ActualFiniteMapDivisorEuler

/-- Actual finite-map divisor Euler change on an arbitrary original field
point. The finite-map datum on the field curve is constructed internally. -/
theorem tensor_invModule_fibre
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} [IsProper c]
    {ε : SchemeHomOver (𝟙 _) c} (F : SmoothProperCurve.FiniteMapData c ε)
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    {I : (pullback c x).IdealSheafData} (hI : I.IsInvertible) {r : ℕ}
    (hZ : IsFinite (I.subschemeι ≫ pullback.snd c x))
    (hdeg : ∀ t : Spec (.of k), (I.subschemeι ≫ pullback.snd c x).finrank t = r)
    (L : (pullback c x).Modules) (hL : Scheme.Modules.IsInvertible L)
    (V : (pullback c x).TwoAffineOpenCover) :
    (Module.finrank k (V.sectionsOf (pullback.snd c x) (L ⊗ I.invModule)).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (pullback.snd c x) (L ⊗ I.invModule)).H1 =
    (Module.finrank k (V.sectionsOf (pullback.snd c x) L).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (pullback.snd c x) L).H1 + r := by
  obtain ⟨a,ha⟩ := Spec.map_surjective x
  letI : Algebra R k := a.hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k = x := ha
  subst x
  exact FourCorner.FieldZeroDivisor.Euler.tensor_invModule_euler_of_finiteMapData
    (SmoothProperCurve.baseChange R c k) (F.baseChange k) hI hZ hdeg L hL V

theorem tensor_lineBundle_fibre
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ε : SchemeHomOver (𝟙 _) c} (F : SmoothProperCurve.FiniteMapData c ε)
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    {r : ℕ} (D : RelEffCartierDiv c r x) (L : (pullback c x).Modules)
    (hL : Scheme.Modules.IsInvertible L) (V : (pullback c x).TwoAffineOpenCover) :
    (Module.finrank k (V.sectionsOf (pullback.snd c x) (L ⊗ D.lineBundle)).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (pullback.snd c x) (L ⊗ D.lineBundle)).H1 =
    (Module.finrank k (V.sectionsOf (pullback.snd c x) L).H0 : ℤ) -
      Module.finrank k (V.sectionsOf (pullback.snd c x) L).H1 + r :=
  tensor_invModule_fibre F x D.isInvertible_I D.isFinite D.finrank_eq L hL V

#print axioms tensor_invModule_fibre
#print axioms tensor_lineBundle_fibre
end FourCorner.ActualFiniteMapDivisorEuler
