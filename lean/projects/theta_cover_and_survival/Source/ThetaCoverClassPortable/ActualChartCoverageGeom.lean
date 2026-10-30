import ThetaCoverClassPortable.ActualChartCoverageHelpers
import ThetaCoverClassPortable.AnyCoverFiniteMapCohomology
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicCurve NeronModelInfra AlgebraicGeometry.RelPicard
open FourCorner.ActualChartFibreH0One.AlgebraicGeometry.RelPicard.ChartAux
universe u
namespace FourCorner.ActualChartCovering
theorem geom
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (F : SmoothProperCurve.FiniteMapData c ε)
    (n g r : ℕ) (hgr : 2 * g < r)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ i, (Dγ i).I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ T) :
    ∃ i : Fin n, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by

  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n:=1)
  haveI : IsSeparated c := inferInstance
  haveI : IsIntegral (pullback c (s ≫ t)) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c (s ≫ t))
  haveI : IsProper (pullback.snd c (s ≫ t)) := inferInstance
  let φ : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) := fibreIso c t s (s ≫ t) rfl

  obtain ⟨εk,⟨Fk⟩⟩ := fieldDatum F (s ≫ t)
  let 𝒱 := Fk.twoAffineOpenCover
  obtain ⟨FF,instFF,instA,M,e,he,⟨Kc,hRR⟩,hch⟩ := hγ K (s ≫ t)
  have hUnit : ∀ V : (pullback c (s ≫ t)).TwoAffineOpenCover,
      chi (pullback.snd c (s ≫ t)) V (𝟙_ _)=1-(g:ℤ) :=
    fun V => unit_euler_of_model_RR Fk M e he Kc g hRR V

  let LY : (pullback c (s ≫ t)).Modules :=
    (Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj L.L
  let TwY : (pullback c (s ≫ t)).Modules := sectionTwist c ε (s ≫ t) r
  have hσ : rigSection c (s ≫ t) ε ≫ pullback.snd c (s ≫ t) = 𝟙 _ := pullback.lift_snd _ _ _
  have hLY : Scheme.Modules.IsInvertible LY := L.isInvertible.pullback _
  have hTwY : Scheme.Modules.IsInvertible TwY :=
    ((Scheme.Hom.isInvertible_ker_of_comp_eq_id (rigSection c (s ≫ t) ε) hσ).pow r).isInvertible_invModule
  have hLT : Scheme.Modules.IsInvertible (LY ⊗ TwY) := hLY.tensor hTwY

  have hAEZ : IsAlgEquivZero (pullback.snd c (s ≫ t)) LY :=
    (((hL K s).pullback φ.inv (fibreIso_inv_fibreAt c t s (s ≫ t) rfl)).of_iso
      (isoPullbackInvOfIso φ (fibreModuleIso c t s (s ≫ t) rfl L.L)).symm)

  have hχLT : (Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0:ℤ)-
      Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H1 =
      (Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ _)).H0:ℤ)-
      Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (𝟙_ _)).H1+r :=
    (ActualFiniteMapEuler.solution (pullback.snd c (s ≫ t)) εk Fk 𝒱 LY TwY hLY hTwY hAEZ).trans
      (origin_twist_euler ε F (s ≫ t) r 𝒱)
  have hpos : 0 < Module.finrank K (𝒱.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ TwY)).H0 := by
    have hu := hUnit 𝒱
    dsimp only [chi] at hu
    omega
  have hnt := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨sec,hsec⟩ := exists_section_ne_zero (pullback.snd c (s ≫ t)) 𝒱 (LY ⊗ TwY) hnt
  obtain ⟨D, -, ⟨eD, -⟩⟩ := FieldZeroDivisor.exists_zero_divisor_over_field_of_finiteMapData F
    (s ≫ t) hLT sec hsec 𝒱 r hχLT
  obtain ⟨Pt, hPt, hDI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D

  haveI : IsCurveOver K FF :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hpt : ∀ m : Fin r, (graphOver c (Pt m) (hPt m) ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun m => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact graphOver_snd c (Pt m) (hPt m)
  have heff : ∀ v : Place K FF, 0 ≤ (∑ m : Fin r, Finsupp.single (M.pointEquivPlace ⟨graphOver c (Pt m) (hPt m) ≫ e.inv, hpt m⟩) (1 : ℤ)) v := by
    classical
    intro v
    rw [Finsupp.finset_sum_apply]
    refine Finset.sum_nonneg fun m _ => ?_
    rw [Finsupp.single_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hdeg : Divisor.degree (∑ m : Fin r, Finsupp.single (M.pointEquivPlace ⟨graphOver c (Pt m) (hPt m) ≫ e.inv, hpt m⟩) (1 : ℤ)) = r := by
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨i, hi⟩ := hch _ heff hdeg

  refine ⟨i, fun 𝒲 => ?_⟩

  generalize hEt : (Dγ i).pullbackAlong t (Category.comp_id t) = Et at ⊢
  let Ei : RelEffCartierDiv c (r - g) (s ≫ t) := Et.pullbackAlong s rfl
  have hγx : ∀ j : Fin (r - g), ((s ≫ t) ≫ (γ i j).1) ≫ c = s ≫ t := fun j => by
    rw [Category.assoc, (γ i j).2, Category.comp_id]
  have hEiI : Ei.I = prodKerGraph c (fun j => (s ≫ t) ≫ (γ i j).1) hγx := by
    have h1 : Ei = (Dγ i).pullbackAlong (s ≫ t) (Category.comp_id _) := by
      show Et.pullbackAlong s rfl = _
      rw [← hEt, RelEffCartierDiv.pullbackAlong_comp]
    rw [h1]
    show (Dγ i).I.comap (mapOnProdOver c (s ≫ t) (Category.comp_id _)) = _
    rw [hDγ i]
    exact prodKerGraph_comap_mapOnProdOver (f := c) (fun j => (γ i j).1) (fun j => (γ i j).2) (s ≫ t)
      (Category.comp_id _)
  have hEi : Scheme.Modules.IsInvertible Ei.idealModule := Ei.isInvertible_I.isInvertible_module
  let Nc : (pullback c (s ≫ t)).Modules := TwY ⊗ Ei.idealModule
  have hNc : Scheme.Modules.IsInvertible Nc := hTwY.tensor hEi

  obtain ⟨eCh⟩ := nonempty_chartModule_iso c t s (s ≫ t) rfl ε r Et
  let eF : fibreModule c t s (L.L ⊗ (sectionTwist c ε t r ⊗ Et.idealModule)) ≅
      (Scheme.Modules.pullback φ.hom).obj (LY ⊗ Nc) :=
    Scheme.Modules.pullbackTensorObjIso (pullback.fst (pullback.snd c t) s) L.L (sectionTwist c ε t r ⊗ Et.idealModule) ≪≫
      (fibreModuleIso c t s (s ≫ t) rfl L.L ⊗ᵢ eCh) ≪≫
      (Scheme.Modules.pullbackTensorObjIso φ.hom LY Nc).symm
  obtain ⟨𝒱', -, -, ⟨g0⟩, ⟨g1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (pullback.snd c (s ≫ t)) (fibreAt c t s) φ.symm (fibreIso_inv_fibreAt c t s (s ≫ t) rfl) 𝒲 _ _
    (isoPullbackInvOfIso φ eF)

  suffices hY : Subsingleton (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 by
    exact Equiv.subsingleton g1.symm.toEquiv

  have hcast : D.lineBundle ⊗ Ei.idealModule =
      (∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module := by
    show D.I.invModule ⊗ Ei.I.module = _
    rw [hDI, hEiI]
    rfl
  let eMN := (α_ LY TwY Ei.idealModule).symm ≪≫ whiskerRightIso eD Ei.idealModule ≪≫ eqToIso hcast
  have hd : Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H0 ∧
      Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H1 ∧
      Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) ((∏ m : Fin r, (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}).1.ker).invModule ⊗
        (∏ j : Fin (r - g), (sectionFibrePoint (γ i j) (s ≫ t)).1.ker).module)).H0 = 1 := by
    obtain ⟨fin0, fin1, hrk⟩ :=
      AlgebraicCurve.CurveModel.finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
        (pullback.snd c (s ≫ t)) M e he
        (fun m : Fin r => (⟨graphOver c (Pt m) (hPt m), graphOver_snd c (Pt m) (hPt m)⟩ :
          {p : Spec (CommRingCat.of K) ⟶ pullback c (s ≫ t) // p ≫ pullback.snd c (s ≫ t) = 𝟙 _}))
        (fun j : Fin (r - g) => sectionFibrePoint (γ i j) (s ≫ t)) 𝒱'
    exact ⟨fin0, fin1, hrk.trans hi⟩
  obtain ⟨fin0, fin1, hrk⟩ := hd
  obtain ⟨⟨k0⟩, ⟨k1⟩⟩ := nonempty_linearEquiv_of_iso (pullback.snd c (s ≫ t)) 𝒱' eMN
  have hM0 : Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H0 = 1 :=
    k0.finrank_eq.trans hrk
  haveI hM1fin : Module.Finite K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 :=
    ActualCohomologyChartInputs.finiteMap_H1_anyCover Fk (LY ⊗ Nc) (hLY.tensor hNc).exists_trivialization 𝒱'


  have hχc := ActualFiniteMapEuler.solution (pullback.snd c (s ≫ t)) εk Fk 𝒱' LY Nc hLY hNc hAEZ
  have hχ' : chi (pullback.snd c (s ≫ t)) 𝒱' Nc=1 := by
    change chi (pullback.snd c (s ≫ t)) 𝒱'
      (sectionTwist c ε (s ≫ t) r ⊗ (Et.pullbackAlong s rfl).idealModule)=1
    rw [←hEt,RelEffCartierDiv.pullbackAlong_comp]
    exact canonical_chart_euler ε F g (r-g) r (by omega) (Dγ i) (s ≫ t) 𝒱' (hUnit 𝒱')
  dsimp only [chi] at hχ'
  have hM1 : Module.finrank K (𝒱'.sectionsOf (pullback.snd c (s ≫ t)) (LY ⊗ Nc)).H1 = 0 := by omega
  exact Module.finrank_zero_iff.mp hM1

end FourCorner.ActualChartCovering
