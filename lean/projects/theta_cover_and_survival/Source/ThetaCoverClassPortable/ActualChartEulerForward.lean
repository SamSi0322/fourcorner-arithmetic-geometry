import ThetaCoverClassPortable.ActualChartFibreH0One
import ThetaCoverClassPortable.ActualFiniteMapDivisorEuler
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
open FourCorner.ActualChartFibreH0One.AlgebraicGeometry.RelPicard.ChartAux
universe u
namespace FourCorner.ActualChartEulerForward

abbrev chi {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (.of k))
    (V : X.TwoAffineOpenCover) (M : X.Modules) : ℤ :=
  (Module.finrank k (V.sectionsOf x M).H0 : ℤ) - Module.finrank k (V.sectionsOf x M).H1

/-- Actual degree Euler change computes the chart twist FROM the known unit
Euler characteristic. No chart Euler hypothesis is used. -/
theorem canonical_twist
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    (g e r : ℕ) (hr : g+e=r) (Dγ : RelEffCartierDiv c e (𝟙 _))
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    (V : (pullback c x).TwoAffineOpenCover)
    (hUnit : chi (pullback.snd c x) V (𝟙_ _) = 1-(g:ℤ)) :
    chi (pullback.snd c x) V
      (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x (Category.comp_id x)).idealModule) = 1 := by
  let hx := Category.comp_id x
  have hσ : rigSection c x ε ≫ pullback.snd c x = 𝟙 _ := pullback.lift_snd _ _ _
  have hIsec : (sectionIdeal c ε x).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c x ε) hσ
  have hIr : ((sectionIdeal c ε x)^r).IsInvertible := hIsec.pow r
  have hP : Scheme.Modules.IsInvertible (sectionTwist c ε x r) := hIr.isInvertible_invModule
  have hEI : (Dγ.pullbackAlong x hx).I.IsInvertible := (Dγ.pullbackAlong x hx).isInvertible_I
  have hPE := hP.tensor hEI.isInvertible_module
  have h2b := ActualFiniteMapDivisorEuler.tensor_lineBundle_fibre F x (Dγ.pullbackAlong x hx)
    (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule) hPE V
  have h2c := eulerChar_congr (pullback.snd c x) V
    (α_ (sectionTwist c ε x r) (Dγ.pullbackAlong x hx).idealModule (Dγ.pullbackAlong x hx).lineBundle ≪≫
      whiskerLeftIso (sectionTwist c ε x r)
        (β_ _ _ ≪≫ (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEI).some) ≪≫
      ρ_ (sectionTwist c ε x r))
  obtain ⟨hZ,hdeg,-,-⟩ :=
    Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (rigSection c x ε) hσ r
  have h2d := ActualFiniteMapDivisorEuler.tensor_invModule_fibre F x hIr hZ hdeg
    (𝟙_ _) (Scheme.Modules.isInvertible_unit _) V
  have h2d' := eulerChar_congr (M := 𝟙_ _ ⊗ ((sectionIdeal c ε x)^r).invModule)
    (M' := sectionTwist c ε x r) (pullback.snd c x) V (λ_ (sectionTwist c ε x r))
  dsimp only [chi] at hUnit ⊢
  omega

theorem chart_twist
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 _) c) (F : SmoothProperCurve.FiniteMapData c ε)
    (g e r : ℕ) (hr : g+e=r) (Dγ : RelEffCartierDiv c e (𝟙 _))
    {k : Type u} [Field k] (x : Spec (.of k) ⟶ Spec (.of R))
    (W : (pullback (pullback.snd c (𝟙 _)) x).TwoAffineOpenCover)
    (hUnit : ∀ V : (pullback c x).TwoAffineOpenCover,
      chi (pullback.snd c x) V (𝟙_ _) = 1-(g:ℤ)) :
    chi (fibreAt c (𝟙 _) x) W
      (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule)) = 1 := by
  obtain ⟨V,⟨e0⟩,⟨e1⟩⟩ := exists_cover_of_cover_chart c (𝟙 _) x x (Category.comp_id _) ε r Dγ W
  dsimp only [chi]
  rw [e0.finrank_eq,e1.finrank_eq]
  exact canonical_twist ε F g e r hr Dγ x V (hUnit V)

/-- Canonical pullback associativity transfers the original curve's actual
unit Euler value to each field fibre after ANY scheme base change. -/
theorem unit_after_baseChange
    {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (t : T ⟶ Spec (.of R)) (g : ℕ)
    (hUnit : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (.of k) ⟶ Spec (.of R)) (V : (pullback c x).TwoAffineOpenCover),
      chi (pullback.snd c x) V (𝟙_ _) = 1-(g:ℤ))
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ T)
    (V : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    chi (fibreAt c t s) V (𝟙_ _) = 1-(g:ℤ) := by
  obtain ⟨W,h0,h1⟩ := exists_cover_of_cover_unit c t s (s ≫ t) rfl V
  dsimp only [chi]
  rw [h0,h1]
  exact hUnit k (s ≫ t) W

#print axioms canonical_twist
#print axioms chart_twist
#print axioms unit_after_baseChange
end FourCorner.ActualChartEulerForward
