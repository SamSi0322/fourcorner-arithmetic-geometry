import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_IsCurveOver
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.NativeCurveModelExistence
import ThetaCoverClassPortable.ActualAllModelGenusBaseChange
import Mathlib.Algebra.CharP.Algebra
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import ThetaCoverClassPortable.ActualThetaSectionQQ
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Divisor_mem_principal_of_forall_ell_pos_add
import ThetaCoverClassPortable.P2M.Util
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.ActualThetaStabilizerQQ

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve~genus"

open scoped CategoryTheory.MonObj

namespace StabJacSol

theorem pullbackSection_zero {X X' : Scheme.{u}} (F : X' ⟶ X) (M : X.Modules) :
    Scheme.Modules.pullbackSection F (0 : 𝟙_ X.Modules ⟶ M) = 0 := by
  haveI : (Scheme.Modules.pullback F).IsLeftAdjoint := ⟨_, ⟨Scheme.Modules.pullbackPushforwardAdjunction F⟩⟩
  haveI : (Scheme.Modules.pullback F).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  rw [Scheme.Modules.pullbackSection_def]
  exact (congrArg ((Scheme.Modules.pullbackUnitIso F).inv ≫ ·) (Functor.map_zero _ _ _)).trans comp_zero

end StabJacSol

open StabJacSol in
theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra ℚ k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    (hsm : Smooth J.toBase) (hpr : IsProper J.toBase) (hgc : GeometricallyConnected J.toBase)
    (g : ℕ)
    (hg : FourCorner.ActualPicardProperties.AllModelRRGenus c g)
    (hg₁ : 1 ≤ g) (r : ℕ) (hr : 2 * g ≤ r) :
    letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
    ∃ θ : 𝟙_ J.P.Modules ⟶ thetaBundle c ε J.toBase h.poincare r (r + 1 - g),
      θ ≠ 0 ∧
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase,
        (∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔
            Scheme.Modules.pullbackSection (z * x).left θ = 0) →
        x = 1 := by
  letI inst := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
  classical

  letI : CharZero k := charZero_of_injective_algebraMap (algebraMap ℚ k).injective
  haveI : IsIntegral (pullback c (𝟙 (Spec (.of k)))) := GeometricallyIntegral.geometrically_isIntegral
    (f:=c) (𝟙 _) (pullback.fst c (𝟙 _)) (pullback.snd c (𝟙 _)) (.of_hasPullback _ _)
  haveI : IsIntegral C := IsIntegral.of_isIso (pullback.fst c (𝟙 _))
  letI := (baseToFunctionField c).toAlgebra
  haveI : IsCurveOver k C.functionField := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    c (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType k C.functionField := essFiniteType_functionField c
  let F := C.functionField
  obtain ⟨M,i,hi,_⟩ := FourCorner.NativeCurveModelExistence.exists_model c
  let e : M.C ≅ C := i.symm
  have he : e.hom ≫ c=M.toBase := by
    change i.inv ≫ c=M.toBase
    have z := congrArg (i.inv ≫ ·) hi
    simpa only [←Category.assoc,Iso.inv_hom_id,Category.id_comp] using z.symm
  obtain ⟨𝔉0,_⟩ := h𝔉 0
  obtain ⟨Kc, g', hRR⟩ := AlgebraicCurve.exists_canonicalDivisor_genus_riemannRoch k F
  obtain rfl : g' = g := FourCorner.ActualPicardProperties.AllModelRRGenus.of_model hg M e he Kc g' hRR

  let ε' : {p : Spec (CommRingCat.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _} :=
    ⟨ε.1 ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact ε.2⟩
  have hε' : ε'.1 ≫ e.hom = ε.1 := by simp [ε']
  let vε : Place k F := M.pointEquivPlace ε'
  haveI : Nonempty (Place k F) := ⟨vε⟩
  have hvε : vε.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed vε

  obtain ⟨θ, hθ⟩ := P2MW.ActualThetaSectionQQ.solution k c ε h𝔉 J h hsm hpr hgc g'
    hg hg₁ r hr

  obtain ⟨pts, hmul, hdict⟩ :=
    RelPicard.exists_pic0_equiv_points_nontrivial_H0_iff_ell_pos k c ε 𝔉0 J h M e he ε' hε'

  have hdeg1 : ∀ n : ℤ, Divisor.degree (Finsupp.single vε n) = n := fun n => by
    rw [Divisor.degree_single, hvε]; simp
  have twist : ∀ (D : Divisor k F), Divisor.degree D = (g' : ℤ) - 1 →
      ∃ Dv : Divisor.degZero (K := k) (F := F),
        (Dv : Divisor k F) + Finsupp.single vε ((g' - 1 : ℕ) : ℤ) = D := by
    intro D hD
    refine ⟨⟨D - Finsupp.single vε ((g' : ℤ) - 1), ?_⟩, ?_⟩
    · show Divisor.degree (D - Finsupp.single vε ((g' : ℤ) - 1)) = 0
      rw [map_sub, hD, hdeg1]; ring
    · have : ((g' - 1 : ℕ) : ℤ) = (g' : ℤ) - 1 := by omega
      simp [this]
  refine ⟨θ, ?_, ?_⟩
  ·
    intro hθ0
    obtain ⟨D, hDdeg, hDell⟩ := AlgebraicCurve.RROpens.exists_degree_eq_sub_one_and_ell_eq_zero Kc g' hRR
    obtain ⟨Dv, hDv⟩ := twist D hDdeg
    have hvan : Scheme.Modules.pullbackSection (pts (Pic0.mk Dv)).left θ = 0 := by
      rw [hθ0]; exact pullbackSection_zero _ _
    have hpos := (hdict Dv (g' - 1)).1 ((hθ _).1 hvan)
    rw [hDv, hDell] at hpos
    exact lt_irrefl _ hpos
  ·
    intro x hx
    obtain ⟨Dξ, hDξ⟩ := Pic0.mk_surjective (pts.symm x)
    have hprin : (Dξ : Divisor k F) ∈ Divisor.principal (K := k) (F := F) := by
      refine AlgebraicCurve.Divisor.mem_principal_of_forall_ell_pos_add Kc g' hRR Dξ (by exact Dξ.2) ?_
      intro D hD hpos
      obtain ⟨Dv, hDv⟩ := twist D hD

      have hz : Scheme.Modules.pullbackSection (pts (Pic0.mk Dv)).left θ = 0 :=
        (hθ _).2 ((hdict Dv (g' - 1)).2 (by rw [hDv]; exact hpos))

      have hzx := (hx (pts (Pic0.mk Dv))).1 hz
      have hprod : pts (Pic0.mk Dv) * x = pts (Pic0.mk (Dv + Dξ)) := by
        rw [Pic0.mk_add, hmul, hDξ, Equiv.apply_symm_apply]
      rw [hprod] at hzx
      have := (hdict (Dv + Dξ) (g' - 1)).1 ((hθ _).1 hzx)

      have hsum : ((Dv + Dξ : Divisor.degZero (K := k) (F := F)) : Divisor k F) +
          Finsupp.single vε ((g' - 1 : ℕ) : ℤ) = D + Dξ := by
        rw [AddMemClass.coe_add, add_right_comm, hDv]
      rwa [hsum] at this

    have hcls : Pic0.mk Dξ = 0 := by
      show (QuotientAddGroup.mk Dξ : Pic0 k F) = 0
      exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 hprin)
    have hx0 : x = pts 0 := by rw [← hcls, hDξ, Equiv.apply_symm_apply]
    have h1 : pts 0 = 1 := by
      have h00 := hmul 0 0
      rw [add_zero] at h00
      exact mul_left_cancel (h00.symm.trans (mul_one _).symm)
    rw [hx0, h1]
