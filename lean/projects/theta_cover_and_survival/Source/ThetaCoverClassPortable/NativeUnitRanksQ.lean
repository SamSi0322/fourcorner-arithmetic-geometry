import ThetaCoverClassPortable.FMDUnitH1
import ThetaCoverClassPortable.NativeCurveModelExistence
import ThetaCoverClassPortable.RiemannRochWithGenusFF
import Mathlib.Algebra.CharP.Algebra
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicCurve NeronModelInfra
namespace FourCorner.ActualPicardProperties

/-- For a QQ-algebra base the genuine native model and RR are constructed;
a supplied all-model RR genus identification then gives the fibre unit ranks.
No scheme H1 or Euler formula is a premise. -/
theorem field_unit_ranks_of_RR_genus
    (R : Type u) [CommRing R] [Algebra ℚ R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hF : ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData c ε, m0 ≤ F.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {k : Type u} [Field k] [IsAlgClosed k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (V : (pullback c s).TwoAffineOpenCover) :
    Module.finrank k (V.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H1 = g ∧
    Module.finrank k (V.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H0 = 1 := by
  obtain ⟨a,ha⟩ := Spec.map_surjective s
  letI : Algebra R k := a.hom.toAlgebra
  letI : Algebra ℚ k := ((algebraMap R k).comp (algebraMap ℚ R)).toAlgebra
  letI : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  have hs : Scheme.TwoAffineOpenCover.specMap R k = s := ha
  subst s
  let s := Scheme.TwoAffineOpenCover.specMap R k
  let Y := pullback c s
  let π := pullback.snd c s
  haveI : IsIntegral Y := GeometricallyIntegral.geometrically_isIntegral
    (f:=c) s (pullback.fst c s) π (.of_hasPullback _ _)
  haveI : IsProper π := MorphismProperty.pullback_snd c s inferInstance
  letI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 π := MorphismProperty.pullback_snd c s inferInstance
  letI := (baseToFunctionField π).toAlgebra
  haveI : IsCurveOver k Y.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one π (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType k Y.functionField := essFiniteType_functionField π
  obtain ⟨M,i,hi,hgeneric⟩ := NativeCurveModelExistence.exists_model π
  let e : M.C ≅ Y := i.symm
  have he : e.hom ≫ π = M.toBase := by
    change i.inv ≫ π = M.toBase
    have z := congrArg (i.inv ≫ ·) hi
    simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using z.symm
  obtain ⟨Kc,hRR⟩ := RiemannRochWithGenusFF.exists_rr (K:=k) (F:=Y.functionField)
  have hg' : genusFF k Y.functionField = g := hg k s Y.functionField M e he Kc _ hRR
  obtain ⟨F,hF0⟩ := hF 0
  exact ⟨(FMDUnitH1.field_H1_eq_genusFF (F.baseChange k) V).trans hg',
    FMDUnitCohomology.field_finrank_H0_unit_eq_one (F.baseChange k) V⟩

end FourCorner.ActualPicardProperties
