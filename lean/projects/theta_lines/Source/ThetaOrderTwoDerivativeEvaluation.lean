import ThetaChartCanonicalFrames
import DoubleZeroDifferential

namespace FourCorner.ThetaOrderTwoDerivativeEvaluation
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaContactDifferentialDivisors ThetaDoubleZeroDifferential
open ResiduePlaceEvaluation SchemePointStalkEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

/-- Exact canonical frame order turns an order-two canonical zero into an
order-two zero of the SAME literal local line equation. -/
theorem function_order_of_frame (w : Place K field) (f : field) (hf : f≠0)
    (ζ : Ω[field⁄K]) (hζ : ζ≠0) (hframe : w.ordDifferential ζ=0)
    (hη : 2≤w.ordDifferential (f • ζ)) : 2≤w.ord f := by
  rw [w.ordDifferential_smul hf (coefficient_ne_zero hζ w),hframe,add_zero] at hη
  exact hη

/-- Evaluation of the actual tangent coefficient vanishes. Both the order
and the coefficient identity concern the native differential and actual DVR. -/
theorem derivative_factor_evaluation (w : Place K field) (hw : w.IsRational)
    (f : field) (hf : f≠0) (ho : 2≤w.ord f)
    (ζ : Ω[field⁄K]) (hζ : ζ≠0) (hframe : w.ordDifferential ζ=0)
    (n : w.toValuationSubring) (hD : KaehlerDifferential.D K field f=(n:field) • ζ) :
    evaluate w hw n=0 := by
  by_cases hn : n=0
  · simp only [hn,map_zero]
  have hnF : (n:field)≠0 := fun h=>hn (Subtype.ext h)
  obtain ⟨c,hc,hm⟩ := derivative_in_maximalIdeal_of_order_ge_two w f hf ho
  have hcF : (c:field)≠0 := by
    rw [hc,hD,w.differentialCoeff_smul]
    exact mul_ne_zero hnF (coefficient_ne_zero hζ w)
  have hc0 : c≠0 := fun h=>hcF (congrArg Subtype.val h)
  have hp := (Place.mem_maximalIdeal_iff_ord_pos' hc0).mp hm
  have he : w.ord (c:field)=w.ord (n:field) := by
    rw [hc]
    change w.ordDifferential (KaehlerDifferential.D K field f)=_
    rw [hD,w.ordDifferential_smul hnF (coefficient_ne_zero hζ w),hframe,add_zero]
  have hnp : 0<w.ord (n:field) := by
    change 0<w.ord (c:field) at hp
    rw [he] at hp
    exact hp
  have hnm := (Place.mem_maximalIdeal_iff_ord_pos' hn).mpr hnp
  rw [←localEval_kernel (evaluate w hw)] at hnm
  exact hnm

#print axioms function_order_of_frame
#print axioms derivative_factor_evaluation
end
end FourCorner.ThetaOrderTwoDerivativeEvaluation
