import ThetaCoverClassPortable.LevelSetImmersion
import ThetaCoverClassPortable.SplitCurveSections
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
  (R : Type u) [CommRing R] [Algebra F R]
  (φ : (R ⊗[F] 𝔉.LevelSet s) ≃ₐ[R] (Fin 𝔉.m → R))

noncomputable def levelSetSections : Fin 𝔉.m → SchemeHomOver (𝟙 _) (baseChange F c R) :=
  FourCorner.SplitCurveSections.splitSection (F := F) (c := c) (B := 𝔉.LevelSet s)
    (ι := 𝔉.levelSetIntoCurve s) (R := R) (m := 𝔉.m) (φ := φ) (𝔉.levelSetIntoCurve_over s)

@[reassoc] theorem levelSetSections_fst (j : Fin 𝔉.m) :
    (𝔉.levelSetSections s R φ j).1 ≫ pullback.fst c (specMap F R) =
      Spec.map (CommRingCat.ofHom
        (FourCorner.SplitAlgebraCoordinates.coordinate F R (𝔉.LevelSet s) 𝔉.m φ j).toRingHom) ≫
        𝔉.levelSetIntoCurve s := pullback.lift_fst _ _ _

theorem levelSetSections_geometric_injective [IsSeparated c]
    (k : Type u) [Field k] (ξ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (fun j => ξ ≫ (𝔉.levelSetSections s R φ j).1) := by
  haveI : IsClosedImmersion (𝔉.levelSetIntoCurve s) := inferInstance
  haveI : Mono (𝔉.levelSetIntoCurve s) := inferInstance
  exact FourCorner.SplitCurveSections.section_geometric_injective F c (𝔉.LevelSet s)
    (𝔉.levelSetIntoCurve s) (𝔉.levelSetIntoCurve_over s) R 𝔉.m φ k ξ

theorem levelSetSections_fibrePoint_injective [IsSeparated c]
    (k : Type u) [Field k] (ξ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (fun j => RelPicard.sectionFibrePoint (𝔉.levelSetSections s R φ j) ξ) := by
  haveI : IsClosedImmersion (𝔉.levelSetIntoCurve s) := inferInstance
  haveI : Mono (𝔉.levelSetIntoCurve s) := inferInstance
  exact FourCorner.SplitCurveSections.sectionFibrePoint_injective F c (𝔉.LevelSet s)
    (𝔉.levelSetIntoCurve s) (𝔉.levelSetIntoCurve_over s) R 𝔉.m φ k ξ

theorem exists_finiteEtale_geometric_sections [Infinite F] [IsIntegral C] [IsSeparated c]
    (hunit : IsUnit (𝔉.m : F)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra F R') (_ : Module.Finite F R')
      (_ : Algebra.Etale F R') (_ : Module.FaithfullyFlat F R') (_ : IsNoetherianRing R')
      (_ : _root_.IsReduced R')
      (σ : Fin 𝔉.m → SchemeHomOver (𝟙 _) (baseChange F c R')),
      ∀ (k : Type u) [Field k] (ξ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')),
        Function.Injective (fun j => ξ ≫ (σ j).1) := by
  obtain ⟨s, _, _, _, _, R', _, _, _, _, _, _, _, ⟨φ⟩⟩ := 𝔉.exists_finiteEtale_splitLevelSet hunit
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, 𝔉.levelSetSections s R' φ,
    fun k _ ξ => 𝔉.levelSetSections_geometric_injective s R' φ k ξ⟩

end AlgebraicGeometry.SmoothProperCurve.FiniteMapData
