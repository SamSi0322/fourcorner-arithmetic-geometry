import ThetaCoverClassPortable.ActualChartFibreH0One
import ThetaCoverClassPortable.ActualFiniteMapDivisorEuler
import ThetaCoverClassPortable.FMDUnitCohomology
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
open FourCorner.ActualChartFibreH0One.AlgebraicGeometry.RelPicard.ChartAux
universe u
namespace FourCorner.ActualChartUnitH1

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (F : SmoothProperCurve.FiniteMapData c ε)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
      (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g := by
  have hx : x ≫ 𝟙 (Spec (CommRingCat.of R)) = x := Category.comp_id x

  obtain ⟨𝒱, -, hH1⟩ := exists_cover_of_cover_unit c (𝟙 _) x x hx 𝒲
  rw [hH1]

  have hχY : (Module.finrank k (𝒱.sectionsOf (pullback.snd c x)
        (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule)).H0 : ℤ) -
      Module.finrank k (𝒱.sectionsOf (pullback.snd c x)
        (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule)).H1 = 1 := by
    obtain ⟨𝒲₂, ⟨e0⟩, ⟨e1⟩⟩ := exists_cover_chart_of_cover c (𝟙 _) x x hx ε r Dγ 𝒱
    rw [← e0.finrank_eq, ← e1.finrank_eq]
    exact hχ k x 𝒲₂

  have hσ : rigSection c x ε ≫ pullback.snd c x = 𝟙 _ := pullback.lift_snd _ _ _
  have hIsec : (sectionIdeal c ε x).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c x ε) hσ
  have hIr : ((sectionIdeal c ε x) ^ r).IsInvertible := hIsec.pow r
  have hP : Scheme.Modules.IsInvertible (sectionTwist c ε x r) := hIr.isInvertible_invModule
  have hEI : (Dγ.pullbackAlong x hx).I.IsInvertible := (Dγ.pullbackAlong x hx).isInvertible_I
  have hPE : Scheme.Modules.IsInvertible (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule) :=
    hP.tensor hEI.isInvertible_module

  have h2b := FourCorner.ActualFiniteMapDivisorEuler.tensor_lineBundle_fibre F x (Dγ.pullbackAlong x hx)
    (sectionTwist c ε x r ⊗ (Dγ.pullbackAlong x hx).idealModule) hPE 𝒱

  have h2c := eulerChar_congr (pullback.snd c x) 𝒱
    (α_ (sectionTwist c ε x r) (Dγ.pullbackAlong x hx).idealModule (Dγ.pullbackAlong x hx).lineBundle ≪≫
      whiskerLeftIso (sectionTwist c ε x r)
        (β_ _ _ ≪≫ (Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEI).some) ≪≫
      ρ_ (sectionTwist c ε x r))

  obtain ⟨hZ, hdeg, -, -⟩ :=
    Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (rigSection c x ε) hσ r
  have h2d := FourCorner.ActualFiniteMapDivisorEuler.tensor_invModule_fibre
    F x hIr hZ hdeg (𝟙_ _) (Scheme.Modules.isInvertible_unit _) 𝒱
  have h2d' := eulerChar_congr (M := 𝟙_ _ ⊗ ((sectionIdeal c ε x) ^ r).invModule)
    (M' := sectionTwist c ε x r) (pullback.snd c x) 𝒱 (λ_ (sectionTwist c ε x r))

  have hG0 := FourCorner.FMDUnitCohomology.finrank_H0_unit_fibre_eq_one F x 𝒱
  omega

#print axioms solution
end FourCorner.ActualChartUnitH1
