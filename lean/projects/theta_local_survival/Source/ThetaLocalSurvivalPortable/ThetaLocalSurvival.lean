import ThetaLocalSurvivalPortable.MultiplicationComponentRealPath

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Topology CategoryTheory.MonObj
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal ComponentDescent

variable (X : Over base) (B : Set X.left) (hBc : IsClosed B)

/-- The actual open subscheme X\B, not an assigned point subset. -/
def boundaryComplement : X.left.Opens := ⟨Bᶜ,hBc.isOpen_compl⟩
def nonboundaryObject : Over base := Over.mk ((boundaryComplement X B hBc).ι≫X.hom)
def nonboundaryInclusion : nonboundaryObject X B hBc ⟶ X :=
  Over.homMk (boundaryComplement X B hBc).ι rfl

theorem nonboundary_point_lift (K : Type) [Field K] [Algebra ℚ K] [TopologicalSpace K]
    (P : KPoints K X) (hP : pointSupport K P∉B) :
    ∃ R : KPoints K (nonboundaryObject X B hBc), R≫nonboundaryInclusion X B hBc=P := by
  letI : IsOpenImmersion (nonboundaryInclusion X B hBc).left :=
    inferInstanceAs (IsOpenImmersion (boundaryComplement X B hBc).ι)
  have hr : pointSupport K P∈Set.range (nonboundaryInclusion X B hBc).left := by
    change pointSupport K P∈Set.range (boundaryComplement X B hBc).ι
    rw [Scheme.Opens.range_ι]
    exact hP
  exact ⟨openPointLift K _ P hr,openPointLift_comp K _ P hr⟩

variable (G : Over base) [GrpObj G] [IsProper G.hom] [GeometricallyIntegral G.hom]
  [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom]
  [hXgi : GeometricallyIntegral X.hom]
  (a : X ⟶ G) (O : rationalBase ⟶ X) (hO : O≫a=1)
  (hB : B.Finite) (hOB : O.left (IsLocalRing.closedPoint ℚ)∈B)
  (V : Set (KPoints ℝ (nonboundaryObject X B hBc)))
  (hV : ∃ P∈V,Joined (rationalScalarPoint ℝ O) (P≫nonboundaryInclusion X B hBc))

include hXgi hOB hB hV in
/-- Exact local-survival conclusion with an actual abelian group scheme, the literal
multiplication pullback, its actual QQ-defined distinguished geometric component, the
actual open subscheme X\B and an arbitrary actual real subset V with the stated path.

This proves the stronger proper-curve version: projectivity is used only through
properness in the paper, and every smooth projective geometrically integral QQ curve
is covered by these hypotheses. No surrogate projectivity or descent flag is introduced. -/
theorem theta_local_survival : ∀ (m : ℕ) (hm : 1≤m),
    Nonempty (pullback (multiplicationComponentToBase G X a O hO m hm) scalarExtension ≅
      (multiplicationGeometricComponentOpen G X a O hO m hm).toScheme) ∧
    ConnectedSpace ↥(pullback (multiplicationComponentToBase G X a O hO m hm) scalarExtension : Scheme) ∧
    ((multiplicationComponentBaseChangeIso G X a O hO m hm).hom ≫
      (multiplicationGeometricComponentOpen G X a O hO m hm).ι ≫
      geometricProjection (multiplicationCoverBase G X a m) ≫
      pullback.fst a.left (multiplication G m) =
        pullback.fst (multiplicationComponentToBase G X a O hO m hm) scalarExtension ≫
          multiplicationComponentProjection G X a O hO m hm) ∧
    (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      ∃ Q : KPoints ℚ_[p] (distinguishedComponentObject G X a O hO m hm),
        ∃ R : KPoints ℚ_[p] (nonboundaryObject X B hBc),
          Q≫distinguishedComponentProjection G X a O hO m hm=R≫nonboundaryInclusion X B hBc) ∧
    (∃ Q : KPoints ℝ (distinguishedComponentObject G X a O hO m hm),
      ∃ R∈V, Q≫distinguishedComponentProjection G X a O hO m hm=R≫nonboundaryInclusion X B hBc) := by
  intro m hm
  refine ⟨⟨multiplicationComponentBaseChangeIso G X a O hO m hm⟩,
    multiplicationComponent_geometric_connected G X a O hO m hm,
    multiplicationComponentBaseChangeIso_projection G X a O hO m hm,?_,?_⟩
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨Q,hQ⟩ := distinguishedComponent_every_padic_nonboundary_point G X a O hO m hm B hB hBc p
    obtain ⟨R,hR⟩ := nonboundary_point_lift X B hBc ℚ_[p]
      (Q≫distinguishedComponentProjection G X a O hO m hm) hQ
    exact ⟨Q,R,hR.symm⟩
  · obtain ⟨R,hRV,hJoin⟩ := hV
    obtain ⟨Q,hQ⟩ := distinguishedComponent_real_point_above_joined G X a O hO m hm
      (R≫nonboundaryInclusion X B hBc) hJoin
    exact ⟨Q,R,hRV,hQ⟩

end FourCorner.ThetaLocalSurvival.StrongTopology
