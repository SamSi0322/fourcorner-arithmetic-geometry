import ThetaCoverClassPortable.FiniteClosedBoundaryPoints
import ThetaCoverClassPortable.MultiplicationComponentLocalCharts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology CategoryTheory.MonObj
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal ComponentDescent

variable (G X : Over base) [GrpObj G] [IsProper G.hom] [GeometricallyIntegral G.hom]
  [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom]
  (a : X ⟶ G) (O : rationalBase ⟶ X) (hO : O≫a=1) (m : ℕ) (hm : 1≤m)
  (B : Set X.left) (hB : B.Finite) (hBc : IsClosed B)

include hB hBc in
/-- Exact nonboundary local-field survival on the actual QQ-defined distinguished
geometric component, for all positive levels and every complete nontrivially normed QQ-field. -/
theorem distinguishedComponent_nonboundary_local_point
    (K : Type) [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K] :
    ∃ Q : KPoints K (distinguishedComponentObject G X a O hO m hm),
      pointSupport K (Q≫distinguishedComponentProjection G X a O hO m hm)∉B := by
  obtain ⟨U,hU,hOU,hLift⟩ := distinguishedComponent_origin_open_image K G X a O hO m hm
  have hInf := smooth_curve_neighborhood_infinite K X (rationalScalarPoint K O) U (hU.mem_nhds hOU)
  have hFin := finite_closed_boundary_points X K B hB hBc
  obtain ⟨P,hPU,hPB⟩ := (hInf.diff hFin).nonempty
  obtain ⟨Q,hQ⟩ := hLift P hPU
  refine ⟨Q,?_⟩
  rw [hQ]
  exact hPB

include hB hBc in
/-- The exact all-finite-places conclusion of local survival, with actual Q_p-valued
scheme points and an actual finite closed boundary. -/
theorem distinguishedComponent_every_padic_nonboundary_point (p : ℕ) [Fact p.Prime] :
    ∃ Q : KPoints ℚ_[p] (distinguishedComponentObject G X a O hO m hm),
      pointSupport ℚ_[p] (Q≫distinguishedComponentProjection G X a O hO m hm)∉B :=
  distinguishedComponent_nonboundary_local_point G X a O hO m hm B hB hBc ℚ_[p]

end FourCorner.ThetaLocalSurvival.StrongTopology
