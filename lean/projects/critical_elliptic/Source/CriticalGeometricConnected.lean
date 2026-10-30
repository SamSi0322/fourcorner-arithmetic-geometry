import CriticalGeometricIntegral
import Mathlib.AlgebraicGeometry.Geometrically.Connected

noncomputable section
namespace FourCorner.CriticalGeometricConnected
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CriticalProj23
universe u
variable {k : Type u} [Field k]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal wording of the paper, derived from the stronger native
geometrical-integrality proof of exactly the same structural morphism. -/
theorem geometricallyConnected (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    GeometricallyConnected (criticalToSpec i) := by
  refine ⟨geometrically_iff_of_commRing.mpr ?_⟩
  intro L _ _ Y fst snd hpb
  haveI := CriticalGeometricIntegral.pullback_integral i hi h2 L
  haveI : Nonempty Y := Nonempty.map hpb.isoPullback.inv.base inferInstance
  haveI : IsIntegral Y := isIntegral_of_isOpenImmersion hpb.isoPullback.hom
  infer_instance
end FourCorner.CriticalGeometricConnected
#print axioms FourCorner.CriticalGeometricConnected.geometricallyConnected
