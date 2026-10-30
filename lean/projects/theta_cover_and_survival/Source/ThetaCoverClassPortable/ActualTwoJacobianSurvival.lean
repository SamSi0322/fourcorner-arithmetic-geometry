import ThetaCoverClassPortable.ActualJacobianGroupObjects
noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Topology CategoryTheory.MonObj
namespace FourCorner.ThetaSurvivingActualJacobians
open ThetaLiteralModels ThetaSurvivingNativeRealPath ThetaSurvivingNativeApplication
open ThetaLocalSurvival.StrongTopology ThetaLocalSurvival.Multiplication ThetaLocalSurvival.Infinitesimal ThetaLocalSurvival.ComponentDescent

def cSurvival (m : ℕ) (hm : 1≤m) : Prop :=
    Nonempty (pullback (multiplicationComponentToBase JC sourceObject iC originalOrigin originalOrigin_iC m hm) scalarExtension ≅
      (multiplicationGeometricComponentOpen JC sourceObject iC originalOrigin originalOrigin_iC m hm).toScheme) ∧
    ConnectedSpace ↥(pullback (multiplicationComponentToBase JC sourceObject iC originalOrigin originalOrigin_iC m hm) scalarExtension : Scheme) ∧
    ((multiplicationComponentBaseChangeIso JC sourceObject iC originalOrigin originalOrigin_iC m hm).hom ≫
      (multiplicationGeometricComponentOpen JC sourceObject iC originalOrigin originalOrigin_iC m hm).ι ≫
      geometricProjection (multiplicationCoverBase JC sourceObject iC m) ≫
      pullback.fst iC.left (multiplication JC m) =
        pullback.fst (multiplicationComponentToBase JC sourceObject iC originalOrigin originalOrigin_iC m hm) scalarExtension ≫
          multiplicationComponentProjection JC sourceObject iC originalOrigin originalOrigin_iC m hm) ∧
    (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      ∃ Q : KPoints ℚ_[p] (distinguishedComponentObject JC sourceObject iC originalOrigin originalOrigin_iC m hm),
        ∃ R : KPoints ℚ_[p] tOpenObject,
          Q≫distinguishedComponentProjection JC sourceObject iC originalOrigin originalOrigin_iC m hm=R≫tOpenInclusion) ∧
    (∃ Q : KPoints ℝ (distinguishedComponentObject JC sourceObject iC originalOrigin originalOrigin_iC m hm),
      ∃ R∈strictRealSet, Q≫distinguishedComponentProjection JC sourceObject iC originalOrigin originalOrigin_iC m hm=R≫tOpenInclusion)

def dSurvival (m : ℕ) (hm : 1≤m) : Prop :=
    Nonempty (pullback (multiplicationComponentToBase JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm) scalarExtension ≅
      (multiplicationGeometricComponentOpen JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm).toScheme) ∧
    ConnectedSpace ↥(pullback (multiplicationComponentToBase JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm) scalarExtension : Scheme) ∧
    ((multiplicationComponentBaseChangeIso JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm).hom ≫
      (multiplicationGeometricComponentOpen JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm).ι ≫
      geometricProjection (multiplicationCoverBase JD sourceObject iD_after_projection m) ≫
      pullback.fst iD_after_projection.left (multiplication JD m) =
        pullback.fst (multiplicationComponentToBase JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm) scalarExtension ≫
          multiplicationComponentProjection JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm) ∧
    (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩
      ∃ Q : KPoints ℚ_[p] (distinguishedComponentObject JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm),
        ∃ R : KPoints ℚ_[p] tOpenObject,
          Q≫distinguishedComponentProjection JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm=R≫tOpenInclusion) ∧
    (∃ Q : KPoints ℝ (distinguishedComponentObject JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm),
      ∃ R∈strictRealSet, Q≫distinguishedComponentProjection JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm=R≫tOpenInclusion)

/-- Both genuine Jacobians, both original maps from the same literal C, all m>=1,
all finite places and the exact strict real U; the same native off-diagonal endpoint
has a real preimage on both distinguished components. No constructor hypothesis remains. -/
theorem cor_theta_surviving_covers : ∀ (m : ℕ) (hm : 1≤m),
    cSurvival m hm ∧ dSurvival m hm ∧
    (∃ Q : KPoints ℝ (distinguishedComponentObject JC sourceObject iC originalOrigin originalOrigin_iC m hm),
      Q≫distinguishedComponentProjection JC sourceObject iC originalOrigin originalOrigin_iC m hm=endpoint) ∧
    (∃ Q : KPoints ℝ (distinguishedComponentObject JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm),
      Q≫distinguishedComponentProjection JD sourceObject iD_after_projection originalOrigin originalOrigin_iD_after_projection m hm=endpoint) ∧
    endpoint∈paperU ∧ endpointY-endpointX=7/300 ∧ endpointX≠endpointY := by
  intro m hm
  refine ⟨native_survival JC iC originalOrigin_iC m hm,
    native_survival JD iD_after_projection originalOrigin_iD_after_projection m hm,?_,?_,
    endpoint_mem_paperU,endpoint_y_sub_x,endpoint_x_ne_y⟩
  · exact (all_m_real_above_native_endpoint JC iC originalOrigin_iC m hm).1
  · exact (all_m_real_above_native_endpoint JD iD_after_projection originalOrigin_iD_after_projection m hm).1

theorem source_is_original_C : sourceObject.left=C ℚ := rfl
theorem c_map_is_original_AJ : iC.left=cAJ.1 := rfl
theorem d_map_is_original_AJ_after_original_projection :
    iD_after_projection.left=ThetaProjection.projection (k:=ℚ)≫dAJ.1 := rfl
end FourCorner.ThetaSurvivingActualJacobians
