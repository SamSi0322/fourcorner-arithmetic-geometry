import ThetaCoverClassPortable.NativeUnitRanksQ
import ThetaCoverClassPortable.ActualAlgEquivZeroEulerIff
import ThetaCoverClassPortable.ActualFiniteMapDivisorEuler
import ThetaCoverClassPortable.FieldZeroDivisorBase
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.ActualPicardSurjectivityQ

set_option autoImplicit false
set_option maxHeartbeats 16000000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.ActualPicardSurjectivityQ.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.ActualPicardSurjectivityQ.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve CategoryTheory.MonoidalCategory Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_preimage Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover RelEffCartierDiv RelEffCartierDiv.twistModule RelEffCartierDiv.twistModule_def Scheme.Modules.rigidifyMapIso prodKerGraph_eq_prod Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.isInvertible_I RelEffCartierDiv.exists_I_eq_prodKerGraph Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd postComp baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut sectionIdeal RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso"
namespace AJSurj
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

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

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

omit [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in

theorem isAlgEquivZero_of_fibrewise {k : Type u} [Field k] [IsAlgClosed k]
    {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε s) (hM : FibrewiseAlgEquivZero M) :
    IsAlgEquivZero (pullback.snd c s) M.L := by
  have h1 := hM k (𝟙 _)
  let e : pullback c s ⟶ pullback (pullback.snd c s) (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift (𝟙 _) (pullback.snd c s) (by simp)
  have he : e ≫ fibreAt c s (𝟙 _) = pullback.snd c s := pullback.lift_snd _ _ _
  have hfst : e ≫ pullback.fst (pullback.snd c s) (𝟙 _) = 𝟙 _ := pullback.lift_fst _ _ _
  refine IsAlgEquivZero.of_iso ?_ (h1.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

omit [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in

theorem nonempty_twoAffineOpenCover (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((pullback c s).TwoAffineOpenCover) := by
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of R ⟶ CommRingCat.of k, Spec.map φ = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  letI : Algebra R k := φ.hom.toAlgebra
  exact ⟨𝔉.twoAffineOpenCover.pullback c k⟩

omit [IsNoetherianRing R] in
theorem core (q : ℚ →+* R) (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε s) (hM : FibrewiseAlgEquivZero M) :
    ∃ E : RelEffCartierDiv c g s, Nonempty (E.twistModule c ε ≅ M.L)  := by
  letI : Algebra ℚ R := q.toAlgebra
  obtain ⟨a,ha⟩ := Spec.map_surjective s
  letI : Algebra R k := a.hom.toAlgebra
  have hs : Scheme.TwoAffineOpenCover.specMap R k = s := ha
  subst s
  let s := Scheme.TwoAffineOpenCover.specMap R k
  obtain ⟨F,hF0⟩ := h𝔉 0
  haveI : IsSeparated c := inferInstance
  haveI : GeometricallyIrreducible c := inferInstance
  haveI : IsProper (pullback.snd c s) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c s) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : IsIntegral (pullback c s) :=
    GeometricallyIntegral.geometrically_isIntegral (f := c) s (pullback.fst c s) (pullback.snd c s)
      (IsPullback.of_hasPullback c s)
  obtain ⟨𝒱⟩ := nonempty_twoAffineOpenCover R c ε h𝔉 s

  have h0 : IsAlgEquivZero (pullback.snd c s) M.L := isAlgEquivZero_of_fibrewise R c ε M hM
  have hχM := FourCorner.ActualAlgEquivZeroEulerIff.eulerChar_eq_of_isAlgEquivZero k (pullback.snd c s) (SmoothProperCurve.sectionBaseChange k ε) (F.baseChange k) M.L M.isInvertible 𝒱 h0

  obtain ⟨hH1,hH0⟩ := FourCorner.ActualPicardProperties.field_unit_ranks_of_RR_genus R c ε h𝔉 g hg s 𝒱

  have hεs : (s ≫ ε.1) ≫ c = s := by rw [Category.assoc, ε.2, Category.comp_id]
  obtain ⟨Eg, hEgI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := c) (g := s)
    (fun _ : Fin g => s ≫ ε.1) (fun _ => hεs)
  have hEginv : Eg.I.IsInvertible := RelEffCartierDiv.isInvertible_I Eg
  have hN : Scheme.Modules.IsInvertible (M.L ⊗ Eg.lineBundle) :=
    M.isInvertible.tensor hEginv.isInvertible_invModule
  have hχ2 := FourCorner.ActualFiniteMapDivisorEuler.tensor_lineBundle_fibre F s Eg M.L M.isInvertible 𝒱

  have hpos : 0 < Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 := by omega
  letI : Nontrivial (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨yv, hyv⟩ := exists_ne (0 : (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 (pullback.snd c s)
    (M.L ⊗ Eg.lineBundle)
  have hσ : eΓ.symm yv ≠ 0 := fun h => hyv (by rw [← eΓ.apply_symm_apply yv, h, map_zero])
  obtain ⟨σ, hσ0⟩ := exists_hom_ne_zero (M.L ⊗ Eg.lineBundle) (eΓ.symm yv) hσ

  have hχ3u : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
            (𝟙_ (pullback c s).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
            (𝟙_ (pullback c s).Modules)).H1 + g := by
    omega
  have hχ3 : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H1 + g := hχ3u
  obtain ⟨E, -, ⟨eE, -⟩⟩ := FourCorner.FieldZeroDivisor.exists_zero_divisor_over_field_of_finiteMapData F
    s hN σ hσ0 𝒱 g hχ3

  have hEg : Eg.I = (sectionIdeal c ε s) ^ g := by
    rw [hEgI, prodKerGraph_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  obtain ⟨eC⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEginv
  have eI : ((sectionIdeal c ε s) ^ g).module ≅ Eg.I.module := eqToIso (by rw [hEg])
  have i1 : E.lineBundle ⊗ ((sectionIdeal c ε s) ^ g).module ≅ M.L :=
    (eE.symm ⊗ᵢ eI) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ eC) ≪≫ (ρ_ _)
  refine ⟨E, ⟨?_⟩⟩
  rw [RelEffCartierDiv.twistModule_def]
  exact Scheme.Modules.rigidifyMapIso _ _ i1 ≪≫ (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified M).some

omit [IsNoetherianRing R] in
theorem main
    (q : ℚ →+* R) (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)} {𝒟 : RelEffCartierDiv c g y} (hU : 𝒟.IsUniversal)
    (aj : Y ⟶ D.P) (haj : aj ≫ D.toBase = y)
    (hclass : Nonempty ((h.poincare.pullbackAlong (⟨aj, haj⟩ : SchemeHomOver y D.toBase)).L ≅ 𝒟.twistModule c ε)) :
    Surjective aj := by
  haveI : IsSeparated c := inferInstance
  refine ⟨fun z => ?_⟩

  let kz := D.P.residueField z
  let k : Type u := AlgebraicClosure kz
  let ι : Spec (CommRingCat.of k) ⟶ D.P :=
    Spec.map (CommRingCat.ofHom (algebraMap kz k)) ≫ D.P.fromSpecResidueField z
  let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := ι ≫ D.toBase
  let tb : SchemeHomOver s D.toBase := ⟨ι, rfl⟩

  let M : RigidifiedLineBundle c ε s := h.poincare.pullbackAlong tb
  have hM : FibrewiseAlgEquivZero M := (algEquivZeroCut c ε).pullback_mem _ _ tb _ h.poincare_mem

  obtain ⟨E, ⟨eE⟩⟩ := core R c ε q h𝔉 g hg s M hM

  let y₀ : Spec (CommRingCat.of k) ⟶ Y := hU.lift E
  have hy₀ : y₀ ≫ y = s := hU.lift_comp E
  let ψ : SchemeHomOver s y := ⟨y₀, hy₀⟩
  have hE : 𝒟.pullbackAlong y₀ hy₀ = E := hU.pullbackAlong_lift E
  let ajO : SchemeHomOver y D.toBase := ⟨aj, haj⟩

  have key : Nonempty ((h.poincare.pullbackAlong (postComp ajO ψ)).L ≅ (h.poincare.pullbackAlong tb).L) := by
    obtain ⟨ecl⟩ := hclass
    obtain ⟨etw⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ 𝒟
    exact ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ajO ψ).symm).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app h.poincare.L).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso ecl ≪≫ etw.symm ≪≫
      eqToIso (congrArg (fun D' => RelEffCartierDiv.twistModule c ε D') hE) ≪≫ eE⟩
  have heq : postComp ajO ψ = tb := h.ext_of_iso s _ _ key
  have hcomp : y₀ ≫ aj = ι := congrArg Subtype.val heq
  refine ⟨y₀ (IsLocalRing.closedPoint k), ?_⟩
  rw [← Scheme.Hom.comp_apply, hcomp]
  exact Scheme.fromSpecResidueField_apply z _

end AlgebraicGeometry.RelPicard.AJSurj

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.ActualPicardSurjectivityQ.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.ActualPicardSurjectivityQ.AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve CategoryTheory.MonoidalCategory"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (q : ℚ →+* R) (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)} {𝒟 : RelEffCartierDiv c g y} (hU : 𝒟.IsUniversal)
    (aj : Y ⟶ D.P) (haj : aj ≫ D.toBase = y)
    (hclass : Nonempty ((h.poincare.pullbackAlong (⟨aj, haj⟩ : SchemeHomOver y D.toBase)).L ≅ 𝒟.twistModule c ε)) :
    Surjective aj :=
  AlgebraicGeometry.RelPicard.AJSurj.main R c ε q h𝔉 g hg D h hU aj haj hclass
