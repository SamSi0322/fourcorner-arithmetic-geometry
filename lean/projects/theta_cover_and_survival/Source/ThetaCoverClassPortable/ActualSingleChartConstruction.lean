import ThetaCoverClassPortable.ActualSingleChartTransport
import ThetaCoverClassPortable.ActualChartTwistExistence
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
open FourCorner.ActualSingleChartTransport.AlgebraicGeometry.RelPicard.ChartOne
universe u
namespace FourCorner.ActualSingleChartConstruction

/-- A genuine universal degree-g effective-divisor parameter space yields the
single native Picard chart and the full original finite-type-test gate.
The universal divisor is supplied by its separate actual construction. -/
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of R)) (𝒟 : RelEffCartierDiv c g y)
    (hU : 𝒟.IsUniversal) :
    ∃ (X : Scheme.{u}) (f : uliftYoneda.{u + 1}.obj X ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      LocallyOfFiniteType (uliftYonedaEquiv f).1 ∧
      ∀ ⦃T : Scheme.{u}⦄ (x : uliftYoneda.{u + 1}.obj T ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
        LocallyOfFiniteType (uliftYonedaEquiv x).1 →
        ∃ (U : T.Opens) (φ : (↑U : Scheme.{u}) ⟶ X),
          (∀ (L : RigidifiedLineBundle c ε (uliftYonedaEquiv x).1), Quotient.mk _ L = (uliftYonedaEquiv x).2.1 →
            ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T),
              Set.range ⇑s ⊆ (U : Set T) ↔
                ∀ (𝒲 : (pullback (pullback.snd c (uliftYonedaEquiv x).1) s).TwoAffineOpenCover),
                  Subsingleton (𝒲.sectionsOf (fibreAt c (uliftYonedaEquiv x).1 s) (fibreModule c (uliftYonedaEquiv x).1 s
                    (L.L ⊗ (sectionTwist c ε (uliftYonedaEquiv x).1 r ⊗
                      (Dγ.pullbackAlong (uliftYonedaEquiv x).1 (Category.comp_id _)).idealModule)))).H1) ∧
          uliftYoneda.{u + 1}.map φ ≫ f = uliftYoneda.{u + 1}.map U.ι ≫ x ∧
          ∀ ⦃T' : Scheme.{u}⦄ (ψ : T' ⟶ T) (φ' : T' ⟶ X),
            LocallyOfFiniteType (ψ ≫ (uliftYonedaEquiv x).1) →
            uliftYoneda.{u + 1}.map φ' ≫ f = uliftYoneda.{u + 1}.map ψ ≫ x →
            ∃ χ : T' ⟶ ↑U, χ ≫ U.ι = ψ ∧ χ ≫ φ = φ' := by
  subst hr

  haveI : IsProper y := hU.isProper

  obtain ⟨DY, hDY⟩ := RelEffCartierDiv.exists_I_eq_mul 𝒟 (Dγ.pullbackAlong y (Category.comp_id y))

  obtain ⟨UY, hUY⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉 y
    (Mγ R c ε (g + e) Dγ y (LY R c ε g e y DY)) (isInvertible_Mγ R c ε (g + e) Dγ y _)
  refine ⟨UY, chartMap R c ε g e y DY UY, ?_, ?_⟩
  ·
    rw [uliftYonedaEquiv_chartMap]
    change LocallyOfFiniteType (UY.ι ≫ y)
    infer_instance
  intro T x hx

  generalize hxa : uliftYonedaEquiv x = a at hx ⊢
  obtain rfl : x = uliftYonedaEquiv.symm a := by rw [← hxa, Equiv.symm_apply_apply]
  clear hxa
  change (relSubPicPresheaf c ε (algEquivZeroCut c ε)).OverTotal T at a
  obtain ⟨t, ⟨ξ, hξ⟩⟩ := a
  obtain ⟨L, rfl⟩ := Quotient.exists_rep ξ
  change FibrewiseAlgEquivZero L at hξ
  haveI : LocallyOfFiniteType t := hx
  change ∃ (U : T.Opens) (φ : (↑U : Scheme.{u}) ⟶ UY), _ ∧
    uliftYoneda.{u + 1}.map φ ≫ _ = uliftYoneda.{u + 1}.map U.ι ≫ uliftYonedaEquiv.symm (pointElem R c ε t L hξ) ∧ _

  obtain ⟨U, hUiff⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉 t
    (Mγ R c ε (g + e) Dγ t L) (isInvertible_Mγ R c ε (g + e) Dγ t L)
  obtain ⟨D, D₀, hD, hDL⟩ := FourCorner.ActualChartTwistExistence.solution R c ε h𝔉 g e (g + e) rfl
    Dγ hχ t L hξ U (fun k _ s hs => (hUiff k s).1 hs)
  refine ⟨U, φ R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL, ?_, ?_, ?_⟩
  · intro L' hL' k _ s
    exact clause_i R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL L' (Quotient.exact hL') k s
  · exact clause_ii R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL
  · intro T' ψ φ' hlft hφ'
    haveI := hlft
    exact clause_iii R c ε h𝔉 g e Dγ hχ y 𝒟 hU DY hDY UY hUY t L hξ U hUiff D D₀ hD hDL ψ φ' hφ'

#print axioms solution
end FourCorner.ActualSingleChartConstruction
