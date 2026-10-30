import ThetaCoverClassPortable.FiniteMapEtaleBridge
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits NeronModelInfra
open scoped TensorProduct
namespace AlgebraicGeometry.SmoothProperCurve.FiniteMapData
variable {F : Type u} [Field F] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of F)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of F))) c}
  (𝔉 : FiniteMapData c ε) (s : F)

noncomputable def levelQuotientMap :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Γ(C, 𝔉.U) →ₐ[F] 𝔉.LevelSet s :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  (Ideal.Quotient.mkₐ F _).comp Algebra.TensorProduct.includeRight

theorem levelQuotientMap_surjective : Function.Surjective (𝔉.levelQuotientMap s) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  exact Ideal.Quotient.mk_surjective.comp
    (Algebra.TensorProduct.includeRight_surjective Γ(C, 𝔉.U) (by simpa using Function.surjective_id))

noncomputable def levelSetIntoU : Spec (CommRingCat.of (𝔉.LevelSet s)) ⟶ 𝔉.U.toScheme :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  Spec.map (CommRingCat.ofHom (𝔉.levelQuotientMap s).toRingHom) ≫ 𝔉.isAffineOpen_U.isoSpec.inv

instance levelSetIntoU_closedImmersion : IsClosedImmersion (𝔉.levelSetIntoU s) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  haveI := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (𝔉.levelQuotientMap s).toRingHom) (𝔉.levelQuotientMap_surjective s)
  unfold levelSetIntoU
  infer_instance

noncomputable def levelSetIntoCurve : Spec (CommRingCat.of (𝔉.LevelSet s)) ⟶ C :=
  𝔉.levelSetIntoU s ≫ 𝔉.U.ι

theorem affineChart_over :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    𝔉.isAffineOpen_U.fromSpec ≫ c = Spec.map (CommRingCat.ofHom (algebraMap F Γ(C, 𝔉.U))) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  rw [← (isAffineOpen_top (Spec (CommRingCat.of F))).SpecMap_appLE_fromSpec c 𝔉.isAffineOpen_U le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem levelSetIntoCurve_over :
    𝔉.levelSetIntoCurve s ≫ c = Spec.map (CommRingCat.ofHom (algebraMap F (𝔉.LevelSet s))) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  unfold levelSetIntoCurve levelSetIntoU
  rw [Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι_assoc,
    𝔉.affineChart_over, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext ((𝔉.levelQuotientMap s).comp_algebraMap)

instance levelSetIntoCurve_closedImmersion [IsSeparated c] : IsClosedImmersion (𝔉.levelSetIntoCurve s) := by
  haveI : IsPreimmersion (𝔉.levelSetIntoCurve s) := by unfold levelSetIntoCurve; infer_instance
  haveI : Module.Finite F (𝔉.LevelSet s) := 𝔉.levelSet_finite F s
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap F (𝔉.LevelSet s)))) :=
    (IsFinite.SpecMap_iff _).mpr (by
      change (algebraMap F (𝔉.LevelSet s)).Finite
      exact RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsProper (𝔉.levelSetIntoCurve s ≫ c) := by rw [𝔉.levelSetIntoCurve_over]; infer_instance
  haveI : IsProper (𝔉.levelSetIntoCurve s) := IsProper.of_comp _ c
  exact IsClosedImmersion.of_isPreimmersion _ (𝔉.levelSetIntoCurve s).isClosedMap.isClosed_range

end AlgebraicGeometry.SmoothProperCurve.FiniteMapData
