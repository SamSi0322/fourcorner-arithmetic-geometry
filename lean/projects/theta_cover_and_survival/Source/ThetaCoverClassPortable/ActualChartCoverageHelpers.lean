import ThetaCoverClassPortable.FMDUnitH1
import ThetaCoverClassPortable.ActualChartFibreH0One
import ThetaCoverClassPortable.ActualFiniteMapDivisorEuler
import ThetaCoverClassPortable.FieldZeroDivisorBase
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicCurve NeronModelInfra AlgebraicGeometry.RelPicard
open FourCorner.ActualChartFibreH0One.AlgebraicGeometry.RelPicard.ChartAux
universe u
namespace FourCorner.ActualChartCovering

/-- The true original FMD and its section are base changed internally. -/
theorem fieldDatum {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 _) c}
    (F : SmoothProperCurve.FiniteMapData c ε) {k : Type u} [Field k]
    (x : Spec (.of k) ⟶ Spec (.of R)) :
    ∃ εk : SchemeHomOver (𝟙 _) (pullback.snd c x),
      Nonempty (SmoothProperCurve.FiniteMapData (pullback.snd c x) εk) := by
  obtain ⟨a,ha⟩ := Spec.map_surjective x
  letI : Algebra R k := a.hom.toAlgebra
  have hx : Scheme.TwoAffineOpenCover.specMap R k=x := ha
  subst x
  exact ⟨SmoothProperCurve.sectionBaseChange k ε,⟨F.baseChange k⟩⟩

abbrev chi {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (.of k)) (V : X.TwoAffineOpenCover) (M : X.Modules) : ℤ :=
  (Module.finrank k (V.sectionsOf x M).H0:ℤ)-Module.finrank k (V.sectionsOf x M).H1

/-- Unit Euler from the actual model/RR supplied by HasChartSections. -/
theorem unit_euler_of_model_RR {k L : Type u} [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    {X : Scheme.{u}} {x : X ⟶ Spec (.of k)} [IsIntegral X] [IsProper x]
    [SmoothOfRelativeDimension 1 x] {ε : SchemeHomOver (𝟙 _) x}
    (F : SmoothProperCurve.FiniteMapData x ε) (M : CurveModel k L)
    (e : M.C ≅ X) (he : e.hom ≫ x=M.toBase) (Kc : Divisor k L) (g : ℕ)
    (hRR : ∀ D : Divisor k L,(ell D:ℤ)-ell (Kc-D)=Divisor.degree D+1-g)
    (V : X.TwoAffineOpenCover) : chi x V (𝟙_ X.Modules)=1-(g:ℤ) := by
  have h0 : Module.finrank k (V.sectionsOf x (𝟙_ X.Modules)).H0=1 :=
    FMDUnitCohomology.field_finrank_H0_unit_eq_one F V
  have h1 := FMDUnitH1.field_H1_eq_of_model_RR F M e he Kc g hRR V
  dsimp only [chi]
  rw [h0,h1]
  rfl

/-- Actual finite-map Euler change for the true degree-r origin twist. -/
theorem origin_twist_euler {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    (r : ℕ) (V : (pullback c x).TwoAffineOpenCover) :
    chi (pullback.snd c x) V (sectionTwist c ε x r)=
      chi (pullback.snd c x) V (𝟙_ _)+r := by
  have hσ : rigSection c x ε ≫ pullback.snd c x=𝟙 _ := pullback.lift_snd _ _ _
  have hI := (Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c x ε) hσ).pow r
  obtain ⟨hZ,hdeg,-,-⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
    (rigSection c x ε) hσ r
  have h := ActualFiniteMapDivisorEuler.tensor_invModule_fibre F x hI hZ hdeg
    (𝟙_ _) (Scheme.Modules.isInvertible_unit _) V
  have he := eulerChar_congr (pullback.snd c x) V (λ_ (sectionTwist c ε x r))
  dsimp only [chi]
  exact he.symm.trans h

/-- The chart degree change is computed, not assumed. -/
theorem canonical_chart_euler {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    (g e r : ℕ) (hr : g+e=r) (Dγ : RelEffCartierDiv c e (𝟙 _))
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    (V : (pullback c x).TwoAffineOpenCover)
    (hUnit : chi (pullback.snd c x) V (𝟙_ _)=1-(g:ℤ)) :
    chi (pullback.snd c x) V
      (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x (Category.comp_id x)).idealModule)=1 := by
  let hx := Category.comp_id x
  have hσ : rigSection c x ε ≫ pullback.snd c x=𝟙 _ := pullback.lift_snd _ _ _
  have hI := (Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c x ε) hσ).pow r
  have hP : Scheme.Modules.IsInvertible (sectionTwist c ε x r) := hI.isInvertible_invModule
  have hEI := (Dγ.pullbackAlong x hx).isInvertible_I
  have h2 := ActualFiniteMapDivisorEuler.tensor_lineBundle_fibre F x (Dγ.pullbackAlong x hx)
    (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule) (hP.tensor hEI.isInvertible_module) V
  have hc := eulerChar_congr (pullback.snd c x) V
    (α_ (sectionTwist c ε x r) (Dγ.pullbackAlong x hx).idealModule (Dγ.pullbackAlong x hx).lineBundle ≪≫
      whiskerLeftIso (sectionTwist c ε x r)
        (β_ _ _ ≪≫ (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEI).some) ≪≫
      ρ_ (sectionTwist c ε x r))
  have ht := origin_twist_euler ε F x r V
  dsimp only [chi] at hUnit ht ⊢
  omega

def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
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

theorem exists_section_ne_zero {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (h : Nontrivial (𝒱.sectionsOf x M).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒱.sectionsOf x M).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x M
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  exact exists_hom_ne_zero M (eΓ.symm y) hσ

end FourCorner.ActualChartCovering
