import ThetaCoverClassPortable.ThetaDPlaneChartSections
import ThetaCoverClassPortable.ThetaTargetSmooth
import ThetaCoverClassPortable.ThetaActualPoints
import ThetaCoverClassPortable.SmoothProperRationalPointPlaces
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ThetaCoverClassPortable.SingleOriginPole
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.DRationalInputs
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaLiteralModels SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces

abbrev curve := D ℚ
abbrev toBase : curve ⟶ Spec (.of ℚ) := dToBase ℚ

theorem integral : IsIntegral curve := ThetaDPlaneChartSections.original_integral
theorem proper : IsProper toBase := d_proper ℚ
theorem smooth : SmoothOfRelativeDimension 1 toBase := ThetaTargetSmooth.target_smooth

local instance : IsIntegral curve := integral
local instance : IsProper toBase := proper
local instance : SmoothOfRelativeDimension 1 toBase := smooth

/-- The literal rational origin [1:1:1] on the original plane quartic. -/
def OD : NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of ℚ))) toBase :=
  ⟨ThetaActualPoints.originD, ThetaSourceComparison.rational_base_unique _ _⟩

abbrev field : Type := curve.functionField
abbrev constants : Algebra ℚ field := fieldAlgebra toBase
local instance : Algebra ℚ field := constants

/-- Its place comes from the actual rational point and actual generic stalk. -/
def originPlace : Place ℚ field := (pointEquivRationalPlace toBase OD).val

theorem originPlace_rational : originPlace.IsRational :=
  (pointEquivRationalPlace toBase OD).property

theorem originPlace_degree_one : originPlace.deg = 1 :=
  originPlace.isRational_iff_deg_eq_one.mp originPlace_rational

theorem originPlace_stalk_range :
    (algebraMap (curve.presheaf.stalk (OD.1 (IsLocalRing.closedPoint ℚ))) field).range =
      originPlace.toValuationSubring.toSubring :=
  pointEquivRationalPlace_range toBase OD

theorem field_isCurveOver : IsCurveOver ℚ field :=
  isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one toBase
    (RingEquiv.refl _) (fun _ => rfl)

theorem field_essFiniteType : Algebra.EssFiniteType ℚ field :=
  essFiniteType_functionField toBase

theorem constantsAreBase : ConstantsAreBase ℚ field := by
  letI := field_isCurveOver
  exact constantsAreBase_of_deg_eq_one originPlace originPlace_degree_one

theorem stichtenothGenusExists : StichtenothGenusExists ℚ field := by
  letI := field_isCurveOver
  letI := field_essFiniteType
  exact stichtenothGenusExists_of_isCurveOver constantsAreBase

/-- Arbitrarily large exact poles only at the ORIGINAL OD, in QQ(D),
with regularity at every other actual rational-base place. No genus input. -/
theorem single_origin_poles (m0 : ℕ) :
    ∃ (f : field) (r : ℕ), f ≠ 0 ∧ m0 < r ∧
      originPlace.ord f = -(r : ℤ) ∧
      (∀ v : Place ℚ field, v ≠ originPlace → 0 ≤ v.ord f) ∧
      Transcendental ℚ f ∧
      FiniteDimensional (IntermediateField.adjoin ℚ ({f} : Set field)) field := by
  letI := field_isCurveOver
  letI := field_essFiniteType
  obtain ⟨f,r,hf,hr,hord,haway⟩ := SingleOriginPole.exists_single_pole_above
    stichtenothGenusExists originPlace originPlace_degree_one m0
  have ht : Transcendental ℚ f := originPlace.transcendental_of_ord_ne_zero (by rw [hord]; omega)
  obtain ⟨x,hx,hfd,_⟩ := IsCurveOver.exists_separating_transcendental (K:=ℚ) (F:=field)
  letI := hfd
  exact ⟨f,r,hf,hr,hord,haway,ht,finiteDimensional_adjoin_of_transcendental x ht⟩

end FourCorner.DRationalInputs
