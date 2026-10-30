import ThetaCoverClassPortable.ActualPic0DictionaryFMD
import ThetaCoverClassPortable.ActualHighDegreeRiemannRoch
import ThetaCoverClassPortable.FMDUnitH1

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 12000000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve NeronModelInfra
open P2MW.ActualPic0DictionaryFMD.AlgebraicGeometry.RelPicard.PtsCoreGlue
universe u
namespace FourCorner.ActualPicardProperties

/-- Genuine all-divisor RR and the actual finite-map datum give the large
section-twist cohomology, through the actual CurveModel divisor-class map. -/
theorem largeDegreeTwist_of_model_RR
    {k F : Type u} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of k)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 _) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (M : CurveModel k F) (e : M.C ≅ C) (he : e.hom ≫ c = M.toBase)
    (εM : {p : Spec (.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (hε : εM.1 ≫ e.hom = ε.1)
    (Kc : Divisor k F) (g : ℕ)
    (hRR : ∀ D : Divisor k F, (ell D : ℤ)-ell (Kc-D)=Divisor.degree D+1-g)
    (L : C.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero c L)
    (r : ℕ) (hr : 2*g ≤ r+1) (V : C.TwoAffineOpenCover) :
    Subsingleton (V.sectionsOf c (L ⊗ ((ε.1.ker)^r).invModule)).H1 ∧
      Module.finrank k (V.sectionsOf c (L ⊗ ((ε.1.ker)^r).invModule)).H0 = r+1-g := by
  let Lm := (Scheme.Modules.pullback e.hom).obj L
  have hLm := hL.pullback e.hom
  have hLm0 := h0.pullback e.hom he
  obtain ⟨cl,hclIso,hclTensor,hclOne,hclPoint,hclNum⟩ := AlgebraicCurve.CurveModel.exists_divisorClassMap M
  let d : Divisor k F := (cl Lm).out
  have hd : (QuotientAddGroup.mk d : Pic k F) = cl Lm := QuotientAddGroup.out_eq' _
  have hei : e.inv ≫ M.toBase = c := by rw [←he,Iso.inv_hom_id_assoc]
  haveI : IsClosedImmersion ε.1 := AlgebraicGeometry.isClosedImmersion_of_comp_eq_id c ε.1 ε.2
  have hI : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε.1 ε.2
  have hIM : εM.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id εM.1 εM.2
  obtain ⟨⟨iker⟩,-⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    e.hom ε.1 εM.1 hε hI hIM r
  let N := Lm ⊗ ((εM.1.ker)^r).invModule
  have hN := hLm.tensor (hIM.pow r).isInvertible_invModule
  let iN : N ≅ (Scheme.Modules.pullback e.hom).obj (L ⊗ ((ε.1.ker)^r).invModule) :=
    (Scheme.Modules.pullbackTensorObjIso e.hom L _ ≪≫ whiskerLeftIso Lm iker).symm
  obtain ⟨VM,_,_,⟨n0⟩,⟨n1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    M.toBase c e he V _ N iN
  have hdeg : Divisor.degree d = 0 := by
    obtain ⟨_,_,_,hχ⟩ := hclNum VM Lm hLm d hd
    let Lc := (Scheme.Modules.pullback e.inv).obj Lm
    obtain ⟨Vc,hc0,hc1,⟨l0⟩,⟨l1⟩⟩ :=
      Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso c M.toBase e.symm hei VM
        Lm Lc (Iso.refl _)
    obtain ⟨Vu,hu0,hu1,⟨u0⟩,⟨u1⟩⟩ :=
      Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso c M.toBase e.symm hei VM
        (𝟙_ M.C.Modules) (𝟙_ C.Modules) (Scheme.Modules.pullbackTensorUnitObjIso e.inv).symm
    have hVu : Vu=Vc := twoAffineOpenCover_ext (hu0.trans hc0.symm) (hu1.trans hc1.symm)
    subst Vu
    have hcC := ActualAlgEquivZeroEulerIff.eulerChar_eq_of_isAlgEquivZero k c ε 𝔉 Lc
      (hLm.pullback e.inv) Vc (hLm0.pullback e.inv hei)
    rw [←l0.finrank_eq,←l1.finrank_eq,←u0.finrank_eq,←u1.finrank_eq] at hχ
    linarith
  let D : Divisor k F := d + r • Finsupp.single (M.pointEquivPlace εM) (1 : ℤ)
  have hD : (QuotientAddGroup.mk D : Pic k F) = cl N := by
    rw [show N = Lm ⊗ ((εM.1.ker)^r).invModule from rfl,hclTensor _ _ hLm (hIM.pow r).isInvertible_invModule,
      (hclPoint εM r).1]
    change QuotientAddGroup.mk (d + r • Finsupp.single (M.pointEquivPlace εM) (1 : ℤ)) = _
    change (QuotientAddGroup.mk d : Pic k F) + QuotientAddGroup.mk _ = _
    rw [hd]
  have hdegD : Divisor.degree D = r := by
    simp only [D,map_add,map_nsmul,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed,nsmul_eq_mul,Nat.cast_one,one_mul,mul_one,hdeg,zero_add]
  obtain ⟨fin0,fin1,hH0,hχ⟩ := hclNum VM N hN D hD
  have hell := high_degree_ell_of_rr Kc g hRR D (by rw [hdegD]; omega)
  have hunit : (Module.finrank k (VM.sectionsOf M.toBase (𝟙_ M.C.Modules)).H0 : ℤ) -
      Module.finrank k (VM.sectionsOf M.toBase (𝟙_ M.C.Modules)).H1 = 1-g := by
    obtain ⟨Vu,_,_,⟨u0⟩,⟨u1⟩⟩ :=
      Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso c M.toBase e.symm hei VM
        (𝟙_ M.C.Modules) (𝟙_ C.Modules) (Scheme.Modules.pullbackTensorUnitObjIso e.inv).symm
    have hz : Module.finrank k (Vu.sectionsOf c (𝟙_ C.Modules)).H0 = 1 :=
      FMDUnitCohomology.field_finrank_H0_unit_eq_one 𝔉 Vu
    rw [←u0.finrank_eq,←u1.finrank_eq,hz,
      FMDUnitH1.field_H1_eq_of_model_RR 𝔉 M e he Kc g hRR Vu]
    rfl
  have hH1zero : Module.finrank k (VM.sectionsOf M.toBase N).H1 = 0 := by
    rw [hH0,hunit,hdegD] at hχ
    omega
  letI := fin1
  haveI : Subsingleton (VM.sectionsOf M.toBase N).H1 := Module.finrank_zero_iff.mp hH1zero
  refine ⟨n1.symm.toEquiv.subsingleton,?_⟩
  rw [←n0.finrank_eq,hH0]
  omega

#print axioms largeDegreeTwist_of_model_RR
end FourCorner.ActualPicardProperties
