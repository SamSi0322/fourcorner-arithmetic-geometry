import ThetaCoverClassPortable.NativeCurveModelExistence
import ThetaCoverClassPortable.ThetaRationalPicardInput
import Mathlib.Algebra.CharP.Algebra

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
open CategoryTheory AlgebraicGeometry AlgebraicCurve CategoryTheory.Limits
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels

/-- Every ACTUAL field-valued geometric base change of the original C/Q has
an actual curve model over that same field. Characteristic zero is DERIVED
from the actual Spec K→Spec Q map, not added as an input. -/
theorem actual_geometric_native_model {K : Type} [Field K]
    (y : Spec (.of K) ⟶ Spec (.of ℚ)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L)
      (M : CurveModel K L) (e : M.C ≅ pullback (cToBase ℚ) y),
      e.hom ≫ pullback.snd (cToBase ℚ) y=M.toBase := by
  obtain ⟨a,ha⟩ := Spec.map_surjective y
  letI : CharZero K := charZero_of_injective_ringHom a.hom.injective
  letI := source_geometricallyIntegral
  letI := source_smooth
  letI := source_proper
  let X := pullback (cToBase ℚ) y
  let c := pullback.snd (cToBase ℚ) y
  letI : IsIntegral X := GeometricallyIntegral.geometrically_isIntegral (f:=cToBase ℚ) y
    (pullback.fst (cToBase ℚ) y) c (.of_hasPullback _ _)
  letI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : SmoothOfRelativeDimension 1 c :=
    MorphismProperty.pullback_snd (cToBase ℚ) y source_smooth
  letI : IsProper c := MorphismProperty.pullback_snd (cToBase ℚ) y source_proper
  letI := SmoothCurveExtension.fieldAlgebra c
  obtain ⟨M,i,hi,hg⟩ := NativeCurveModelExistence.exists_model c
  refine ⟨X.functionField,inferInstance,inferInstance,M,i.symm,?_⟩
  change i.inv ≫ c=M.toBase
  have hh := congrArg (fun q : X ⟶ Spec (.of K) => i.inv ≫ q) hi
  simpa only [←Category.assoc,Iso.inv_hom_id,Category.id_comp] using hh.symm

#print axioms actual_geometric_native_model
end FourCorner.ThetaRationalPicardInput
