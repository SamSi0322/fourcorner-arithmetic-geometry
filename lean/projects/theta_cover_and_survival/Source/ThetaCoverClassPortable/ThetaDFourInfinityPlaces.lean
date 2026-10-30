import ThetaCoverClassPortable.ThetaDOriginalChartOpens
import ThetaCoverClassPortable.ThetaDGlobalSheafBasis
import ThetaCoverClassPortable.ThetaDInfinityPoints
import ThetaCoverClassPortable.SmoothProperRationalPointPlaces

namespace FourCorner.ThetaDFourInfinityPlaces
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections
open ThetaDNativeProjRatios ThetaDOriginalChartOpens ThetaDChartNaturality
open SmoothProperClosedPointPlaces SmoothProperRationalPointPlaces SchemePointStalkEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra

abbrev Parameters := {a : K // a∈ThetaDInfinityPoints.parameters}

def actualPoint (a : Parameters) : RationalPoint toBase :=
  ⟨ThetaDInfinityPoints.parametrizedPoint a,
    ThetaDInfinityPoints.point_over _ _⟩

def closedPoint (a : Parameters) : closedPoints geometricD :=
  closedPointOfPoint toBase (actualPoint a).val (actualPoint a).property

def place (a : Parameters) : Place K field :=
  (pointEquivRationalPlace toBase (actualPoint a)).val

 theorem closedPoint_injective : Function.Injective closedPoint := by
  intro a b h
  apply ThetaDInfinityPoints.parametrizedPoint_injective
  apply SchemePointStalkEvaluation.point_ext toBase
    (ThetaDInfinityPoints.parametrizedPoint a) (ThetaDInfinityPoints.parametrizedPoint b)
    (actualPoint a).property (actualPoint b).property
  exact congrArg Subtype.val h

 theorem place_injective : Function.Injective place := by
  intro a b h
  have he : pointEquivRationalPlace toBase (actualPoint a)=
      pointEquivRationalPlace toBase (actualPoint b) := Subtype.ext h
  have hp := (pointEquivRationalPlace toBase).injective he
  exact ThetaDInfinityPoints.parametrizedPoint_injective (congrArg Subtype.val hp)

 theorem closedPoint_at_infinity (a : Parameters) : (closedPoint a).val∉geoU 2 := by
  let vals : Fin 2 → K := ![a.val,0]
  let hv := ThetaDInfinityPoints.relations a.val (ThetaDInfinityPoints.parameter_isRoot a.val a.property)
  let e := ThetaDGeometricChartPoints.evaluation 0 vals hv
  let x : Spec (.of (chartRing 0)) := Spec.map (CommRingCat.ofHom e.toRingHom) (IsLocalRing.closedPoint K)
  have hx : x∉PrimeSpectrum.basicOpen (Ideal.Quotient.mk _ (X (1:Fin 2))) := by
    change ¬(e (Ideal.Quotient.mk _ (X (1:Fin 2)))∉(IsLocalRing.closedPoint K).asIdeal)
    simp [e,ThetaDGeometricChartPoints.evaluation_X,vals]
  have ho : chartMap 0 x∉B 2 := by
    change x∉chartMap 0 ⁻¹ᵁ B (ThetaAmbientChart.insert 2 0 1)
    rw [chart_preimage_basic]
    exact hx
  change pullback.fst (dToBase ℚ) qb
    (ThetaDInfinityPoints.parametrizedPoint a (IsLocalRing.closedPoint K))∉U 2
  rw [U_eq_basic]
  change (ThetaDGeometricChartPoints.point 0 vals hv ≫ pullback.fst (dToBase ℚ) qb)
    (IsLocalRing.closedPoint K)∉B 2
  simp only [ThetaDGeometricChartPoints.point,pullback.lift_fst]
  exact ho

 theorem place_eq_closedPoint (a : Parameters) : place a=placeOfClosedPoint toBase (closedPoint a) := rfl

/-- The four literal roots at infinity are FOUR DISTINCT actual places of
the actual original geometric curve, and all have positive canonical order. -/
theorem place_order_positive (a : Parameters) :
    0<(place a).ordDifferential ThetaDActualDifferential.omega := by
  rw [place_eq_closedPoint]
  exact ThetaDGlobalCanonicalCandidate.infinity_order_positive (closedPoint a) (closedPoint_at_infinity a)

 theorem four_places : Nat.card (Set.range place)=4 := by
  rw [←Nat.card_congr (Equiv.ofInjective place place_injective)]
  simp [ThetaDInfinityPoints.parameters_card]

 theorem four_closedPoints : Nat.card (Set.range closedPoint)=4 := by
  rw [←Nat.card_congr (Equiv.ofInjective closedPoint closedPoint_injective)]
  simp [ThetaDInfinityPoints.parameters_card]

#print axioms closedPoint_injective
#print axioms place_injective
#print axioms closedPoint_at_infinity
#print axioms place_order_positive
#print axioms four_places
end
end FourCorner.ThetaDFourInfinityPlaces
