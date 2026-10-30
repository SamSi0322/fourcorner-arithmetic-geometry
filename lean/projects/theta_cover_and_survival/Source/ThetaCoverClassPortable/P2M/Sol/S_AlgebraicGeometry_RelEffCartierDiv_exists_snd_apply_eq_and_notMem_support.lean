import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.finite_preimage_singleton SmoothOfRelativeDimension.smooth SmoothOfRelativeDimension IsProper Scheme.Hom Scheme.Hom.range_fiberι GeometricallyIrreducible IsFinite Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Scheme Smooth IsReduced smoothOfRelativeDimension_isStableUnderBaseChange Scheme.IdealSheafData isIntegral_of_irreducibleSpace_of_isReduced RelEffCartierDiv isReduced_of_smooth_over_field"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "I isFinite"
namespace OffSupportSol
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x : T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support := by
  classical
  let q := pullback.snd c t

  haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hsm1 : SmoothOfRelativeDimension 1 q := MorphismProperty.pullback_snd c t inferInstance
  have hsm2 : SmoothOfRelativeDimension 1 (q.fiberToSpecResidueField x) :=
    MorphismProperty.pullback_snd q (T.fromSpecResidueField x) hsm1
  haveI : IsIntegral (q.fiber x) :=
    GeometricallyIntegral.geometrically_isIntegral (f := q)
      (T.fromSpecResidueField x) (q.fiberι x) (q.fiberToSpecResidueField x)
      (IsPullback.of_hasPullback _ _)
  have hinf : Infinite ↥(q.fiber x) := by
    have h := @AlgebraicCurve.infinite_setOf_isClosed_singleton _ _ _ (q.fiberToSpecResidueField x) inferInstance hsm2
    haveI := h.to_subtype
    exact Infinite.of_injective (fun z : {y : ↥(q.fiber x) | IsClosed ({y} : Set ↥(q.fiber x))} => (z : ↥(q.fiber x)))
      Subtype.val_injective

  haveI : IsFinite (D.I.subschemeι ≫ q) := D.isFinite
  have hfin : ((D.I.subschemeι ≫ q).base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton _ x

  by_contra hcon
  push_neg at hcon
  have hsub : ∀ z : ↥(q.fiber x), ∃ w : ↥(D.I.subscheme), D.I.subschemeι.base w = (q.fiberι x).base z := by
    intro z
    have hx : q.base ((q.fiberι x).base z) = x := by
      have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
        rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
      exact this
    have hmem := hcon _ hx
    have : (q.fiberι x).base z ∈ Set.range D.I.subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hmem
    exact this
  choose w hw using hsub
  have hwS : ∀ z, w z ∈ (D.I.subschemeι ≫ q).base ⁻¹' {x} := by
    intro z
    show q.base (D.I.subschemeι.base (w z)) ∈ ({x} : Set T)
    rw [hw z]
    have : (q.fiberι x).base z ∈ q.base ⁻¹' {x} := by
      rw [← Scheme.Hom.range_fiberι]; exact ⟨z, rfl⟩
    exact this
  haveI : Finite ↥((D.I.subschemeι ≫ q).base ⁻¹' {x}) := hfin.to_subtype
  have hinj : Function.Injective (fun z : ↥(q.fiber x) => (⟨w z, hwS z⟩ : ↥((D.I.subschemeι ≫ q).base ⁻¹' {x}))) := by
    intro z₁ z₂ h12
    have h' : w z₁ = w z₂ := congrArg Subtype.val h12
    have := (hw z₁).symm.trans ((congrArg (fun v => D.I.subschemeι.base v) h') ▸ (hw z₂))
    exact (q.fiberι x).isEmbedding.injective (by rw [← hw z₁, ← hw z₂, h'])
  haveI := Finite.of_injective _ hinj
  exact not_finite ↥(q.fiber x)

end AlgebraicGeometry.RelEffCartierDiv.OffSupportSol

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x : T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support :=
  AlgebraicGeometry.RelEffCartierDiv.OffSupportSol.main c t D x
