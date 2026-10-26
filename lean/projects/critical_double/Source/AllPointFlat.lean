import AllPointSchemeProperties
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.AllPointFlat
open SmoothProperPlaceNaturality
variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [Algebra Y.functionField X.functionField]

theorem all_stalks_flat (cY : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 cY]
    (π : X ⟶ Y)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y)) :
    ∀x:X,(π.stalkMap x).hom.Flat := by
  intro x
  let A := Y.presheaf.stalk (π x)
  let B := X.presheaf.stalk x
  letI : ValuationRing A := valuationRing_stalk_of_smoothOfRelativeDimension_one cY (π x)
  let f : A →+* B := (π.stalkMap x).hom
  have hf : Function.Injective f := by
    intro a b hab
    apply IsFractionRing.injective A Y.functionField
    apply (algebraMap Y.functionField X.functionField).injective
    rw [stalk_field_naturality π hg x a,stalk_field_naturality π hg x b]
    exact congrArg (algebraMap B X.functionField) hab
  letI : Algebra A B := f.toAlgebra
  haveI : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hf
  haveI : Module.Flat A B := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem flat_of_generic_diagram (cY : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 cY]
    (π : X ⟶ Y)
    (hg : X.fromSpecStalk (genericPoint X) ≫ π=
      Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
        Y.fromSpecStalk (genericPoint Y)) : Flat π :=
  HasRingHomProperty.of_stalkMap RingHom.Flat.ofLocalizationPrime (all_stalks_flat cY π hg)

#print axioms all_stalks_flat
#print axioms flat_of_generic_diagram
end FourCorner.AllPointFlat
