import ThetaCoverClassPortable.NativeSurvivalApplication
import ThetaCoverClassPortable.ThetaCSchemeBoundaryFinite
noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Topology CategoryTheory.MonObj
namespace FourCorner.ThetaSurvivingNativeApplication
open ThetaLiteralModels ThetaSurvivingNativeRealPath
open ThetaLocalSurvival.StrongTopology ThetaLocalSurvival.Multiplication ThetaLocalSurvival.Infinitesimal ThetaLocalSurvival.ComponentDescent
/-- Finiteness of the full closed scheme boundary, by residue-field classification of every scheme point. -/
theorem literalBoundary_finite : literalBoundary.Finite :=
  ThetaCSchemeBoundaryFinite.boundary_finite
theorem native_survival (G : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] (a : sourceObject ⟶ G)
    (hO : originalOrigin≫a=1) : ∀ (m : ℕ) (hm : 1≤m),
    Nonempty (pullback (multiplicationComponentToBase G sourceObject a originalOrigin hO m hm) scalarExtension ≅
      (multiplicationGeometricComponentOpen G sourceObject a originalOrigin hO m hm).toScheme) ∧
    ConnectedSpace ↥(pullback (multiplicationComponentToBase G sourceObject a originalOrigin hO m hm) scalarExtension : Scheme) ∧
    ((multiplicationComponentBaseChangeIso G sourceObject a originalOrigin hO m hm).hom ≫
      (multiplicationGeometricComponentOpen G sourceObject a originalOrigin hO m hm).ι ≫
      geometricProjection (multiplicationCoverBase G sourceObject a m) ≫
      pullback.fst a.left (multiplication G m) =
        pullback.fst (multiplicationComponentToBase G sourceObject a originalOrigin hO m hm) scalarExtension ≫
          multiplicationComponentProjection G sourceObject a originalOrigin hO m hm) ∧
    (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      ∃ Q : KPoints ℚ_[p] (distinguishedComponentObject G sourceObject a originalOrigin hO m hm),
        ∃ R : KPoints ℚ_[p] tOpenObject,
          Q≫distinguishedComponentProjection G sourceObject a originalOrigin hO m hm=R≫tOpenInclusion) ∧
    (∃ Q : KPoints ℝ (distinguishedComponentObject G sourceObject a originalOrigin hO m hm),
      ∃ R∈strictRealSet, Q≫distinguishedComponentProjection G sourceObject a originalOrigin hO m hm=R≫tOpenInclusion) :=
  native_survival_on_tOpen_of_boundary_finite G a hO literalBoundary_finite

end FourCorner.ThetaSurvivingNativeApplication
