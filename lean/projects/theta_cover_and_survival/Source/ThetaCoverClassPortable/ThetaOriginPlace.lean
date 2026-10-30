import ThetaCoverClassPortable.ThetaRationalPicardInput
import ThetaCoverClassPortable.SmoothProperRationalPointPlaces
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.ThetaRationalPicardInput
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaLiteralModels SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces

local instance sourceIntegral : IsIntegral (C ℚ) := ThetaSourceComparison.source_integral
local instance sourceSmooth : SmoothOfRelativeDimension 1 (cToBase ℚ) := source_smooth
local instance sourceProper : IsProper (cToBase ℚ) := source_proper
local instance constants : Algebra ℚ (C ℚ).functionField := fieldAlgebra (cToBase ℚ)

/-- The actual degree-one place of the actual rational origin in the native
function field of the original C; no replacement field or Pic1 point. -/
def originPlace : Place ℚ (C ℚ).functionField :=
  (pointEquivRationalPlace (cToBase ℚ) OC).val

theorem originPlace_rational : originPlace.IsRational :=
  (pointEquivRationalPlace (cToBase ℚ) OC).property

theorem originPlace_degree_one : originPlace.deg=1 :=
  originPlace.isRational_iff_deg_eq_one.mp originPlace_rational

/-- The place preserves the SAME actual native stalk embedding. -/
theorem originPlace_stalk_range :
    (algebraMap ((C ℚ).presheaf.stalk (OC.1 (IsLocalRing.closedPoint ℚ)))
      (C ℚ).functionField).range=originPlace.toValuationSubring.toSubring :=
  pointEquivRationalPlace_range (cToBase ℚ) OC

#print axioms originPlace
#print axioms originPlace_degree_one
#print axioms originPlace_stalk_range
end FourCorner.ThetaRationalPicardInput
