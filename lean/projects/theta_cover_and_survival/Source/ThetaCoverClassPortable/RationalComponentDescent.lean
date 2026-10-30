import ThetaCoverClassPortable.GeometricGaloisFibres
import ThetaCoverClassPortable.ClosedOrbitComponentDescent
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace FourCorner.ThetaLocalSurvival.ComponentDescent
variable {Y : Scheme} (f : Y ⟶ qqBase)

theorem geometricScheme_noetherian [IsProper f] : NoetherianSpace (geometricScheme f) := by
  letI : IsProper (geometricToOmega f) := inferInstance
  letI : IsLocallyNoetherian (geometricScheme f) := LocallyOfFiniteType.isLocallyNoetherian (geometricToOmega f)
  letI : CompactSpace (geometricScheme f) := QuasiCompact.compactSpace_of_compactSpace (geometricToOmega f)
  letI : IsNoetherian (geometricScheme f) :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  infer_instance

variable (O : qqBase ⟶ Y) (hO : O ≫ f=𝟙 qqBase)

theorem geometricOriginPoint_projection : geometricProjection f (geometricOriginPoint f O hO)=
    O (IsLocalRing.closedPoint ℚ) := by
  change (geometricOrigin f O hO ≫ geometricProjection f) (IsLocalRing.closedPoint Omega)=_
  simp only [geometricOrigin,geometricProjection,pullback.lift_fst,Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim (α:=PrimeSpectrum ℚ) _ _

/-- Effective QQ descent of the ACTUAL geometric connected component
containing the ACTUAL rational origin. Its full preimage equality is
proved from the actual projection, actual Galois action and prime-fibre
transitivity, not from invariant labels alone. -/
theorem rational_origin_component_descends [IsProper f] :
    ∃U : Y.Opens,IsClopen (U:Set Y) ∧
      geometricProjection f ⁻¹' (U:Set Y)=connectedComponent (geometricOriginPoint f O hO) ∧
      O (IsLocalRing.closedPoint ℚ)∈U := by
  letI := geometricScheme_noetherian f
  obtain ⟨S,hS,hpre,hpoint⟩ := closed_orbit_component_descent
    (geometricProjection f) (geometricProjection_closed f) (geometricProjection_surjective f)
    (geometricHomeomorph f) (geometricOriginPoint f O hO)
    (geometricOriginPoint_fixed f O hO) (geometricProjection_fibre_orbit f)
  refine ⟨⟨S,hS.isOpen⟩,hS,hpre,?_⟩
  rw [geometricOriginPoint_projection] at hpoint
  exact hpoint

/-- The geometric component, as an actual open subscheme of the actual
geometric scalar extension. -/
def geometricComponentOpen [IsProper f] : (geometricScheme f).Opens := by
  letI := geometricScheme_noetherian f
  exact ⟨connectedComponent (geometricOriginPoint f O hO),
    (noetherian_connectedComponent_isClopen (geometricOriginPoint f O hO)).isOpen⟩

end FourCorner.ThetaLocalSurvival.ComponentDescent
