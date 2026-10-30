import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ThetaCoverClassPortable.ActualFibrePoincareTwistQQ
import ThetaCoverClassPortable.ActualAllModelGenusBaseChange
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_thetaBundle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_translate_thetaBundle_tensor_iso
import ThetaCoverClassPortable.ActualThetaStabilizerQQ
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_forall_pullbackSection_eq_zero_iff
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected
import ThetaCoverClassPortable.P2M.Util
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.ActualThetaCubeFBSQQ

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve~genus"

open scoped CategoryTheory.MonObj


theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra ℚ k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    (hsm : Smooth J.toBase) (hpr : IsProper J.toBase) (hgc : GeometricallyConnected J.toBase)
    (g : ℕ)
    (hg : FourCorner.ActualPicardProperties.AllModelRRGenus c g) (hg₁ : 1 ≤ g)
    (r : ℕ) (hr : 2 * g ≤ r) :
    Scheme.Modules.FiniteBySections
      ((thetaBundle c ε J.toBase h.poincare r (r + 1 - g)).tensorPow 3) J.toBase := by

  letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
  haveI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).isCommMonObj
  haveI : IsProper J.toBase := hpr

  haveI : IsIntegral J.P :=
    AlgebraicGeometry.isIntegral_of_smooth_of_geometricallyConnected k J.toBase hsm hgc (η[Over.mk J.toBase]).left
      (by simpa using Over.w (η[Over.mk J.toBase]))

  obtain ⟨𝔉, -⟩ := h𝔉 0
  have hg' := hg
  have hfib := P2MW.ActualFibrePoincareTwistQQ.solution k c ε (algebraMap ℚ k) 𝔉 J h g hg' r (by omega)
  have hΘ : Scheme.Modules.IsInvertible (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) :=
    RelPicard.isInvertible_thetaBundle k c ε h𝔉 h.poincare r (r + 1 - g) hfib

  have hsq := fun x y => RelPicard.nonempty_translate_thetaBundle_tensor_iso k c ε h𝔉 J h hsm hpr hgc g hg r hr x y
  obtain ⟨θ, hθ, hK⟩ :=
    P2MW.ActualThetaStabilizerQQ.solution k c ε h𝔉 J h hsm hpr hgc g hg hg₁ r hr

  obtain ⟨N, σ, U, hU, hfr⟩ :=
    Scheme.Modules.exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso k J.toBase
      (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) hΘ hsq θ hθ
  obtain ⟨𝔓, -, -⟩ :=
    Scheme.Modules.exists_projPresentation_of_iSup_eq_top J.toBase
      ((thetaBundle c ε J.toBase h.poincare r (r + 1 - g)).tensorPow 3) N σ U hU (fun i V hV => hfr i le_top hV)
  have hfin : IsFinite 𝔓.toProj :=
    Scheme.Modules.ProjPresentation.isFinite_toProj_of_forall_pullbackSection_eq_zero_iff k J.toBase
      (thetaBundle c ε J.toBase h.poincare r (r + 1 - g)) hΘ hsq θ hK 𝔓
  exact ⟨N,𝔓,hfin⟩
