import ThetaCoverClassPortable.FiniteAlgebraPointFibres
import Mathlib.Topology.Covering.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
namespace FourCorner.ThetaLocalSurvival.StrongTopology

variable (A S K : Type) [CommRing A] [CommRing S] [Algebra ℚ A]
  [Algebra A S] [Algebra ℚ S] [IsScalarTower ℚ A S]
  [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K] [ProperSpace K]
  [Module.Finite A S] [Algebra.Etale A S]

/-- The actual map of field-valued points of a finite etale algebra is closed for local fields. -/
theorem finite_etale_affine_points_closed :
    IsClosedMap (fun f : S →ₐ[ℚ] K => f.comp (Algebra.algHom ℚ A S)) := by
  let P := Algebra.Presentation.ofFinitePresentation A S
  have h := (finite_algebra_solution_projection_closed A S K P).comp
    (presentationPointsHomeomorph ℚ A K S P).isClosedMap
  exact h

/-- Every actual finite etale map of finite-type QQ-affine schemes is a covering
on genuine strong-topology local-field points, with no assumed analytic properness. -/
theorem finite_etale_affine_points_covering [Algebra.FiniteType ℚ A] :
    IsCoveringMap (fun f : S →ₐ[ℚ] K => f.comp (Algebra.algHom ℚ A S)) := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply (finite_etale_affine_points_closed A S K).isCoveringMapOn_of_isLocalHomeomorphOn
  · intro φ _
    change {f : S →ₐ[ℚ] K | f.comp (Algebra.algHom ℚ A S)=φ}.Finite
    exact finite_algebra_point_fibres A S K φ
  · exact (etale_affine_points_localHomeomorph A S K).isLocalHomeomorphOn

end FourCorner.ThetaLocalSurvival.StrongTopology
