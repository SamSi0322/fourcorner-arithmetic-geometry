import ThetaCoverClassPortable.ActualAlgEquivZeroEulerIff
import ThetaCoverClassPortable.ActualFiniteMapDivisorEuler
import ThetaCoverClassPortable.FieldZeroDivisorBase
import ThetaCoverClassPortable.ActualPic0DictionaryFMD
import ThetaCoverClassPortable.FiniteMapDataBaseChange
import ThetaCoverClassPortable.FMDUnitH1
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.ActualAlgZeroPointsFMD

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry P2MW.ActualAlgZeroPointsFMD.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.ActualAlgZeroPointsFMD.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom Spec IsIntegral Scheme Scheme.Modules.Hom.app IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero RelEffCartierDiv RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I Scheme.IdealSheafData.IsInvertible Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv.isInvertible_I SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover prodKerGraph prodKerGraph_eq_prod   RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed RelEffCartierDiv.exists_I_eq_prodKerGraph   Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "IsAlgEquivZero Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso pointsSubBasepointModule  nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule"
namespace DivRep
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem twoAffineOpenCover_ext {X : Scheme.{u}} {𝒱 𝒲 : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) : 𝒱 = 𝒲 := by
  obtain ⟨U0, U1, p1, p2, p3, p4⟩ := 𝒱
  obtain ⟨U0', U1', q1, q2, q3, q4⟩ := 𝒲
  change U0 = U0' at h0
  change U1 = U1' at h1
  subst h0
  subst h1
  rfl

noncomputable def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     show (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  show (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

theorem main
    {k : Type u} [Field k] [IsAlgClosed k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsProper a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData a ε, m₀ ≤ 𝔉.m) {L : A.Modules}
    (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero a L) :
    ∃ Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a),
      Nonempty ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) := by

  haveI : IsSeparated a := inferInstance
  haveI : GeometricallyIrreducible a := inferInstance
  haveI : IsProper (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : IsIntegral (pullback a (𝟙 (Spec (CommRingCat.of k)))) :=
    GeometricallyIntegral.geometrically_isIntegral (f := a) (𝟙 (Spec (CommRingCat.of k)))
      (pullback.fst a (𝟙 _)) (pullback.snd a (𝟙 _)) (IsPullback.of_hasPullback a (𝟙 _))
  haveI : IsIso (pullback.fst a (𝟙 (Spec (CommRingCat.of k)))) := inferInstance

  obtain ⟨𝔉, -⟩ := h𝔉 0
  let 𝒱A : A.TwoAffineOpenCover := 𝔉.twoAffineOpenCover
  let φ : pullback a (𝟙 (Spec (CommRingCat.of k))) ≅ A := asIso (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))
  have hφ : φ.hom ≫ a = pullback.snd a (𝟙 (Spec (CommRingCat.of k))) := by
    show pullback.fst a (𝟙 (Spec (CommRingCat.of k))) ≫ a = pullback.snd a (𝟙 (Spec (CommRingCat.of k)))
    exact pullback.condition.trans (Category.comp_id _)
  let L' : (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules :=
    (Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).obj L
  have hL' : Scheme.Modules.IsInvertible L' := hL.pullback _
  obtain ⟨𝒱, hU0, hU1, ⟨eH0u⟩, ⟨eH1u⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) a φ hφ 𝒱A (𝟙_ A.Modules)
      (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)
      (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).symm
  obtain ⟨𝒱₂, hU0₂, hU1₂, ⟨eH0L⟩, ⟨eH1L⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) a φ hφ 𝒱A (L ⊗ 𝟙_ A.Modules) L'
      ((Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).mapIso (ρ_ L).symm)
  have h𝒱 : 𝒱₂ = 𝒱 := twoAffineOpenCover_ext (hU0₂.trans hU0.symm) (hU1₂.trans hU1.symm)
  subst h𝒱

  have hχ0 := FourCorner.ActualAlgEquivZeroEulerIff.eulerChar_eq_of_isAlgEquivZero k a ε 𝔉 L hL 𝒱A h0
  have hχA := (P2MW.ActualPic0DictionaryFMD.AlgebraicGeometry.RelPicard.PtsCoreGlue.eulerChar_congr
    a 𝒱A (ρ_ L)).trans hχ0
  have n1 := eH0u.finrank_eq
  have n2 := eH1u.finrank_eq
  have n3 := eH0L.finrank_eq
  have n4 := eH1L.finrank_eq

  let d : ℕ := Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
    (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1
  obtain ⟨E, hEI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := a) (g := 𝟙 (Spec (CommRingCat.of k)))
    (fun _ : Fin d => ε.1) (fun _ => ε.2)
  have hEinv : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I E
  have hLE : Scheme.Modules.IsInvertible (L' ⊗ E.lineBundle) := hL'.tensor hEinv.isInvertible_invModule
  have hχ2 := FourCorner.ActualFiniteMapDivisorEuler.tensor_lineBundle_fibre 𝔉
    (𝟙 (Spec (CommRingCat.of k))) E L' hL' 𝒱₂

  have hpos : (Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
        (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1 : ℤ)
      ≤ ((Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H0 : ℤ)
          - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H1)
        - ((Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
              (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H0 : ℤ)
            - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
              (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1) := by
    omega
  haveI : IsIntegral A := IsIntegral.of_isIso φ.hom
  have hu0A : Module.finrank k (𝒱A.sectionsOf a (𝟙_ A.Modules)).H0 = 1 :=
    FourCorner.FMDUnitCohomology.field_finrank_H0_unit_eq_one 𝔉 𝒱A
  have hu0 : Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (.of k))))
      (𝟙_ (pullback a (𝟙 (Spec (.of k)))).Modules)).H0 = 1 :=
    eH0u.finrank_eq.trans hu0A
  have hpos0 : 0 < Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (.of k))))
      (L' ⊗ E.lineBundle)).H0 := by omega
  letI : Nontrivial (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (.of k)))) (L' ⊗ E.lineBundle)).H0 :=
    Module.nontrivial_of_finrank_pos hpos0
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱₂
    (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  obtain ⟨s, hs⟩ := exists_hom_ne_zero (L' ⊗ E.lineBundle) (eΓ.symm y) hσ

  have hχ3 : (Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H1
      = (Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
            (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
            (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1 + d := by
    omega
  obtain ⟨D, -, ⟨eD, -⟩⟩ := FourCorner.FieldZeroDivisor.exists_zero_divisor_over_field_of_finiteMapData
    𝔉 (𝟙 (Spec (CommRingCat.of k))) hLE s hs 𝒱₂ d hχ3

  obtain ⟨P, hP, hDI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D

  have hE : E.I = (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ d := by
    rw [hEI, prodKerGraph_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, RelEffCartierDiv.ofPoint_I]
  obtain ⟨eE⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEinv
  obtain ⟨eT⟩ := RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule ε P hP
  have hcast : D.lineBundle ⊗ E.I.module =
      (prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ d).module := by
    show D.I.invModule ⊗ E.I.module = _
    rw [hDI, hE]
  refine ⟨List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a), ⟨?_⟩⟩
  exact (ρ_ L').symm ≪≫ whiskerLeftIso L' eE.symm ≪≫ (α_ L' E.I.invModule E.I.module).symm ≪≫
    whiskerRightIso eD E.I.module ≪≫ eqToIso hcast ≪≫ eT

end AlgebraicGeometry.RelPicard.DivRep

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsProper a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData a ε, m₀ ≤ 𝔉.m) {L : A.Modules}
    (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero a L) :
    ∃ Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a),
      Nonempty ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) :=
  AlgebraicGeometry.RelPicard.DivRep.main ε h𝔉 hL h0
