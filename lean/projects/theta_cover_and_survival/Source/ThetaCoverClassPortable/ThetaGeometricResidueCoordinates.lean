import ThetaCoverClassPortable.ThetaGeometricPointCoordinateEvaluation

namespace FourCorner.ThetaGeometricResidueCoordinates
open AlgebraicGeometry AlgebraicCurve CategoryTheory MvPolynomial
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates ThetaDCoordinateBasicOpens
open ThetaGeometricPointCoordinateEvaluation SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces
open SchemePointStalkEvaluation ResiduePlaceEvaluation
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance (j : Fin 3) : Nonempty (geoU j) := geoU_nonempty j

variable (j : Fin 3) (vals : Fin 2 → K)
    (hv : ∀a : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation j a)=0)

def chartPoint : RationalPoint toBase :=
  ⟨ThetaDGeometricChartPoints.point j vals hv,ThetaDGeometricChartPoints.point_over j vals hv⟩

def rationalPlace : {w : Place K field // w.IsRational} :=
  pointEquivRationalPlace toBase (chartPoint j vals hv)

/-- Literal chart coordinates as actual elements of the place's ACTUAL
valuation ring, using the native original point's actual stalk. -/
def coordinateValue (a : Fin 2) : (rationalPlace j vals hv).val.toValuationSubring :=
  stalkValuationEquiv toBase
    (closedPointOfPoint toBase (chartPoint j vals hv).val (chartPoint j vals hv).property)
      (geometricD.presheaf.germ (geoU j)
        ((chartPoint j vals hv).val (IsLocalRing.closedPoint K))
        (geometric_point_in_chart j vals hv) (coordinateSection j a))

 theorem coordinateValue_coe (a : Fin 2) :
    (coordinateValue j vals hv a : field)=coordinate j a := by
  rw [coordinateValue,stalkValuationEquiv_coe]
  exact geometricD.algebraMap_germ_eq_germToFunctionField
    (geometric_point_in_chart j vals hv) (coordinateSection j a)

/-- The actual residue evaluation, induced by the actual over-K scheme
point and point-place equivalence, gives the ORIGINAL literal coordinate. -/
theorem evaluate_coordinateValue (a : Fin 2) :
    evaluate (rationalPlace j vals hv).val (rationalPlace j vals hv).property
      (coordinateValue j vals hv a)=vals a := by
  have hh := pointEquivRationalPlace_evaluate toBase (chartPoint j vals hv)
    (geometricD.presheaf.germ (geoU j)
      ((chartPoint j vals hv).val (IsLocalRing.closedPoint K))
      (geometric_point_in_chart j vals hv) (coordinateSection j a))
  exact hh.trans (coordinate_stalk_evaluation j vals hv a)

/-- The genuine evaluation kernel is exactly the actual DVR maximal ideal;
polynomial vanishing can therefore be transferred to geometric orders. -/
theorem evaluation_kernel :
    RingHom.ker (evaluate (rationalPlace j vals hv).val (rationalPlace j vals hv).property).toRingHom=
      IsLocalRing.maximalIdeal (rationalPlace j vals hv).val.toValuationSubring :=
  localEval_kernel _

#print axioms coordinateValue_coe
#print axioms evaluate_coordinateValue
#print axioms evaluation_kernel
end
end FourCorner.ThetaGeometricResidueCoordinates
