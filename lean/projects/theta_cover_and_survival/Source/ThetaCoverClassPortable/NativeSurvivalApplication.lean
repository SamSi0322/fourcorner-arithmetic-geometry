import ThetaCoverClassPortable.NativeCurveInput
import ThetaCoverClassPortable.ThetaBoundary
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Topology CategoryTheory.MonObj
namespace FourCorner.ThetaSurvivingNativeApplication
open ThetaLiteralModels ThetaSurvivingNativeRealPath
open ThetaLocalSurvival.StrongTopology ThetaLocalSurvival.Multiplication ThetaLocalSurvival.Infinitesimal ThetaLocalSurvival.ComponentDescent
/-- Full underlying scheme boundary, including nonrational and generic points. -/
def literalBoundary : Set (C ℚ) := (sourceTOpen : Set (C ℚ))ᶜ
theorem literalBoundary_closed : IsClosed literalBoundary := sourceTOpen.isOpen.isClosed_compl
abbrev literalNonboundary := nonboundaryObject sourceObject literalBoundary literalBoundary_closed
abbrev literalInclusion := nonboundaryInclusion sourceObject literalBoundary literalBoundary_closed
/-- The complement open is exactly the original T-nonzero open. -/
theorem literalComplement_eq : boundaryComplement sourceObject literalBoundary literalBoundary_closed = sourceTOpen := by
  ext x
  simp [boundaryComplement,literalBoundary]
theorem literalNonboundary_eq_tOpenObject : literalNonboundary = tOpenObject := by
  unfold literalNonboundary nonboundaryObject
  rw [literalComplement_eq]
  rfl
def literalOpenIso : literalNonboundary ≅ tOpenObject :=
  eqToIso literalNonboundary_eq_tOpenObject
/-- The open-scheme identification retains the original map to C. -/
theorem literalOpenIso_projection : literalOpenIso.hom≫tOpenInclusion=literalInclusion := by
  have aux (U V : (C ℚ).Opens) (h : U=V) :
      (eqToIso (congrArg (fun W : (C ℚ).Opens => (Over.mk (W.ι≫cToBase ℚ) : Over base)) h)).hom ≫
        (Over.homMk V.ι rfl : Over.mk (V.ι≫cToBase ℚ) ⟶ sourceObject) =
      (Over.homMk U.ι rfl : Over.mk (U.ι≫cToBase ℚ) ⟶ sourceObject) := by
    subst V
    simp
  exact aux _ _ literalComplement_eq
/-- The paper's exact U, using the actual open inclusion and canonical real points. -/
def literalV : Set (KPoints ℝ literalNonboundary) := {R | R≫literalInclusion∈paperU}
theorem literalV_joined : ∃ P∈literalV, Joined (rationalScalarPoint ℝ originalOrigin) (P≫literalInclusion) := by
  obtain ⟨P,hP⟩ := nonboundary_point_lift sourceObject literalBoundary literalBoundary_closed ℝ endpoint (by
    change ¬¬pointSupport ℝ endpoint∈sourceTOpen
    exact not_not.mpr endpoint_T_nonzero)
  refine ⟨P,?_,?_⟩
  · change P≫literalInclusion∈paperU
    rw [hP]
    exact endpoint_mem_paperU
  · rw [hP]
    exact ⟨originalRealPath⟩
theorem originalOrigin_mem_boundary : originalOrigin.left (IsLocalRing.closedPoint ℚ)∈literalBoundary := by
  change ¬originalOrigin.left (IsLocalRing.closedPoint ℚ)∈sourceTOpen
  intro h
  have he := ThetaBoundary.boundaryPoint_boundary (k:=ℚ) (fun _=>true)
  have hm : (IsLocalRing.closedPoint ℚ)∈(ThetaActualPoints.boundaryPoint (k:=ℚ) (fun _=>true)) ⁻¹ᵁ ThetaBoundary.tOpen := h
  rw [he] at hm
  exact hm
theorem native_survival_of_boundary_finite (G : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] (a : sourceObject ⟶ G)
    (hO : originalOrigin≫a=1) (hB : literalBoundary.Finite) : ∀ (m : ℕ) (hm : 1≤m),
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
        ∃ R : KPoints ℚ_[p] (nonboundaryObject sourceObject literalBoundary literalBoundary_closed),
          Q≫distinguishedComponentProjection G sourceObject a originalOrigin hO m hm=R≫nonboundaryInclusion sourceObject literalBoundary literalBoundary_closed) ∧
    (∃ Q : KPoints ℝ (distinguishedComponentObject G sourceObject a originalOrigin hO m hm),
      ∃ R∈literalV, Q≫distinguishedComponentProjection G sourceObject a originalOrigin hO m hm=R≫nonboundaryInclusion sourceObject literalBoundary literalBoundary_closed) :=
  theta_local_survival sourceObject literalBoundary literalBoundary_closed G a originalOrigin hO hB originalOrigin_mem_boundary literalV literalV_joined

/-- Every distinguished component has a real point above this same native off-diagonal endpoint. -/
theorem all_m_real_above_native_endpoint (G : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] (a : sourceObject ⟶ G)
    (hO : originalOrigin≫a=1) (m : ℕ) (hm : 1≤m) :
    (∃ Q : KPoints ℝ (distinguishedComponentObject G sourceObject a originalOrigin hO m hm),
      Q≫distinguishedComponentProjection G sourceObject a originalOrigin hO m hm=endpoint) ∧
      endpoint∈paperU ∧ endpointY-endpointX=7/300 ∧ endpointX≠endpointY := by
  refine ⟨?_,endpoint_mem_paperU,endpoint_y_sub_x,endpoint_x_ne_y⟩
  exact distinguishedComponent_real_point_above_joined G sourceObject a originalOrigin hO m hm endpoint ⟨originalRealPath⟩
theorem native_survival_on_tOpen_of_boundary_finite (G : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] (a : sourceObject ⟶ G)
    (hO : originalOrigin≫a=1) (hB : literalBoundary.Finite) : ∀ (m : ℕ) (hm : 1≤m),
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
      ∃ R∈strictRealSet, Q≫distinguishedComponentProjection G sourceObject a originalOrigin hO m hm=R≫tOpenInclusion) := by
  intro m hm
  obtain ⟨hi,hc,hproj,hp,hr⟩ := native_survival_of_boundary_finite G a hO hB m hm
  refine ⟨hi,hc,hproj,?_,?_⟩
  · intro p hpPrime
    letI : Fact p.Prime := ⟨hpPrime⟩
    obtain ⟨Q,R,hQR⟩ := hp p hpPrime
    refine ⟨Q,R≫literalOpenIso.hom,?_⟩
    simpa only [Category.assoc,literalOpenIso_projection] using hQR
  · obtain ⟨Q,R,hRV,hQR⟩ := hr
    refine ⟨Q,R≫literalOpenIso.hom,?_,?_⟩
    · change R≫literalInclusion∈paperU at hRV
      change (R≫literalOpenIso.hom)≫tOpenInclusion∈paperU
      simpa only [Category.assoc,literalOpenIso_projection] using hRV
    · simpa only [Category.assoc,literalOpenIso_projection] using hQR

end FourCorner.ThetaSurvivingNativeApplication
