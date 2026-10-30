import ThetaCoverClassPortable.ThetaCoverFunctions
import ThetaCoverClassPortable.ThetaGeometricResidueCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits MvPolynomial
namespace FourCorner.ThetaCoverBoundaryPoints
attribute [local instance] Classical.propDecidable
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates ThetaDChartNaturality
open ThetaGeometricResidueCoordinates ThetaGeometricPointCoordinateEvaluation
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : CharZero field := charZero_of_injective_algebraMap (algebraMap K field).injective

abbrev Signs := Bool × Bool
abbrev sign {k : Type*} [Field k] [CharZero k] (b : Bool) : k := ThetaActualPoints.sign b
abbrev values (e : Signs) : Fin 2 → K := ![sign e.1,sign e.2]

theorem relations (e : Signs) (a : Fin 1) :
    MvPolynomial.aeval (values e) (ThetaDGeometricChartPoints.equation 2 a)=0 := by
  rcases e with ⟨b,c⟩
  cases b <;> cases c <;> fin_cases a <;>
    norm_num [values,ThetaActualPoints.sign,ThetaDGeometricChartPoints.equation,
      ThetaQuotientChart.affineEquation,ThetaAmbientChart.dehom,ThetaLiteralModels.targetEquation,
      ThetaLiteralModels.targetPolynomial,ThetaTargetSmooth.drop_table,Fin.isValue] <;> simp <;> norm_num

/-- The four literal [epsilon:eta:1] as ACTUAL points, not four place labels. -/
def point (e : Signs) : SmoothProperRationalPointPlaces.RationalPoint toBase :=
  chartPoint 2 (values e) (relations e)

def place (e : Signs) : Place K field := (rationalPlace 2 (values e) (relations e)).val

theorem point_injective : Function.Injective point := by
  intro e d he
  have hv := ThetaDGeometricChartPoints.point_injective 2 (values e) (values d)
    (relations e) (relations d) (congrArg Subtype.val he)
  apply Prod.ext
  · apply ThetaActualPoints.sign_injective (k:=K)
    exact congrFun hv 0
  · apply ThetaActualPoints.sign_injective (k:=K)
    exact congrFun hv 1

theorem place_injective : Function.Injective place := by
  intro e d he
  apply point_injective
  apply (SmoothProperRationalPointPlaces.pointEquivRationalPlace toBase).injective
  exact Subtype.ext he

/-- Sum of the four genuine native point-places, each with coefficient one. -/
def boundarySum : Divisor K field := ∑e : Signs,Finsupp.single (place e) 1

theorem boundarySum_effective : 0≤boundarySum := by
  intro w
  simp only [boundarySum,Finsupp.finsetSum_apply,Finsupp.single_apply]
  exact Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num)

theorem degree_boundarySum : Divisor.degree boundarySum=4 := by
  simp [boundarySum,map_sum,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]

theorem boundarySum_apply (w : Place K field) :
    boundarySum w=if ∃e,place e=w then 1 else 0 := by
  classical
  by_cases hw : ∃e,place e=w
  · obtain ⟨e,rfl⟩ := hw
    simp only [boundarySum,Finsupp.finsetSum_apply,Finsupp.single_apply,place_injective.eq_iff]
    simp
  · have hn : ∀e,place e≠w := fun e he=>hw ⟨e,he⟩
    simp only [boundarySum,Finsupp.finsetSum_apply,Finsupp.single_apply]
    simp [hn]

/-- The chart coordinates at each actual E, in its actual native DVR. -/
def xValue (e : Signs) : (place e).toValuationSubring := coordinateValue 2 (values e) (relations e) 0
def yValue (e : Signs) : (place e).toValuationSubring := coordinateValue 2 (values e) (relations e) 1
 theorem xValue_coe (e : Signs) : (xValue e:field)=x := coordinateValue_coe 2 _ _ 0
 theorem yValue_coe (e : Signs) : (yValue e:field)=y := coordinateValue_coe 2 _ _ 1
 theorem xValue_eval (e : Signs) :
    ResiduePlaceEvaluation.evaluate (place e) (rationalPlace 2 (values e) (relations e)).property (xValue e)=sign e.1 :=
  evaluate_coordinateValue 2 _ _ 0
 theorem yValue_eval (e : Signs) :
    ResiduePlaceEvaluation.evaluate (place e) (rationalPlace 2 (values e) (relations e)).property (yValue e)=sign e.2 :=
  evaluate_coordinateValue 2 _ _ 1

#print axioms place_injective
#print axioms degree_boundarySum
end FourCorner.ThetaCoverBoundaryPoints
