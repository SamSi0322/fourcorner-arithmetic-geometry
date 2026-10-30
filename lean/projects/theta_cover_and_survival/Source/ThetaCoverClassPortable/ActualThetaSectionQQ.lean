import Mathlib.AlgebraicGeometry.Geometrically.Connected
import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ThetaCoverClassPortable.Definitions.Def_JacJ1Iface
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModel
import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pullbackSection_thetaBundle_eq_zero_iff
import ThetaCoverClassPortable.ActualRigidifiedFibreTwistQQ
import ThetaCoverClassPortable.ActualAllModelGenusBaseChange
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.ActualThetaSectionQQ

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve~genus"

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
    ∃ θ : 𝟙_ J.P.Modules ⟶ thetaBundle c ε J.toBase h.poincare r (r + 1 - g),
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase,
        Scheme.Modules.pullbackSection x.left θ = 0 ↔
          ∀ 𝒲 : (pullback (pullback.snd c J.toBase) x.left).TwoAffineOpenCover,
            Nontrivial (𝒲.sectionsOf (fibreAt c J.toBase x.left)
              (fibreModule c J.toBase x.left (h.poincare.L ⊗ sectionTwist c ε J.toBase (g - 1)))).H0 := by
  haveI : Smooth J.toBase := hsm
  obtain ⟨𝔉, -⟩ := h𝔉 0

  have hg' := hg

  have hfib := P2MW.ActualRigidifiedFibreTwistQQ.solution
    k c ε (algebraMap ℚ k) 𝔉 g hg' h.poincare h.poincare_mem r (by omega)

  obtain ⟨θ, hθ⟩ := AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff
    k c ε h𝔉 h.poincare r (r + 1 - g) (g - 1) (by omega) hfib
  exact ⟨θ, fun x => hθ k x.left⟩
