import ThetaCoverClassPortable.FiniteEtaleSchemeCovering
import ThetaCoverClassPortable.MultiplicationComponentFinitePlaces
import Mathlib.Topology.Homotopy.Lifting

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology CategoryTheory.MonObj
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal ComponentDescent

variable (G X : Over base) [GrpObj G] [IsProper G.hom] [GeometricallyIntegral G.hom]
  [IsProper X.hom] (a : X ⟶ G) (O : rationalBase ⟶ X) (hO : O≫a=1) (m : ℕ) (hm : 1≤m)

/-- The genuine distinguished QQ component is a covering of the real strong-point space. -/
theorem distinguishedComponent_real_covering :
    IsCoveringMap (fun Q : KPoints ℝ (distinguishedComponentObject G X a O hO m hm) =>
      Q≫distinguishedComponentProjection G X a O hO m hm) := by
  obtain ⟨hf,he⟩ := multiplicationComponentProjection_finite_etale G X a O hO m hm
  letI : IsFinite (distinguishedComponentProjection G X a O hO m hm).left := hf
  letI : Etale (distinguishedComponentProjection G X a O hO m hm).left := he
  exact finite_etale_scheme_points_covering ℝ (distinguishedComponentProjection G X a O hO m hm)

/-- Every actual real point joined to O lifts to the actual distinguished QQ component.
The lifted path lies in that component because its whole codomain is that actual scheme. -/
theorem distinguishedComponent_real_point_above_joined
    (P : KPoints ℝ X) (hP : Joined (rationalScalarPoint ℝ O) P) :
    ∃ Q : KPoints ℝ (distinguishedComponentObject G X a O hO m hm),
      Q≫distinguishedComponentProjection G X a O hO m hm=P := by
  let γ := hP.somePath
  have hzero : γ.toContinuousMap 0=
      distinguishedComponentScalarOrigin ℝ G X a O hO m hm≫
        distinguishedComponentProjection G X a O hO m hm := by
    rw [distinguishedComponentScalarOrigin_projection]
    exact γ.source
  obtain ⟨Γ,hΓ,_⟩ := (distinguishedComponent_real_covering G X a O hO m hm).exists_path_lifts
    γ.toContinuousMap (distinguishedComponentScalarOrigin ℝ G X a O hO m hm) hzero
  exact ⟨Γ 1,(congrFun hΓ 1).trans γ.target⟩

end FourCorner.ThetaLocalSurvival.StrongTopology
