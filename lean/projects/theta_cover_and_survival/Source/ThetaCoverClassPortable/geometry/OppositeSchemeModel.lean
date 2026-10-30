import ThetaCoverClassPortable.geometry.SchemeModelFiniteExtension
import ThetaCoverClassPortable.geometry.OppositeTensorFractionField
import ThetaCoverClassPortable.geometry.OppositeRegularDifferentials

noncomputable section
namespace FourCorner.OppositeSchemeModel
open AlgebraicCurve AlgebraicGeometry OppositeCoordinateAlgebra
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The actual smooth proper model of the literal opposite-pair function field,
constructed by gluing normalized affine charts. -/
def model (mu nu : K) : CurveModel K (functionField mu nu) :=
  SchemeModelFiniteExtension.model K (functionField mu nu)

theorem model_integral (mu nu : K) : IsIntegral (model mu nu).C := inferInstance
theorem model_proper (mu nu : K) : IsProper (model mu nu).toBase := inferInstance
theorem model_smooth (mu nu : K) : SmoothOfRelativeDimension 1 (model mu nu).toBase :=
  inferInstance

/-- The equivalence maps the original scalar constants to the scheme's base map. -/
def functionFieldEquiv (mu nu : K) :
    letI := (model mu nu).functionFieldAlgebra
    functionField mu nu ≃ₐ[K] (model mu nu).C.functionField :=
  (model mu nu).ffAlgEquiv

theorem functionFieldEquiv_constants (mu nu a : K) :
    (model mu nu).ffEquiv (algebraMap K (functionField mu nu) a) =
      baseToFunctionField (model mu nu).toBase a :=
  (model mu nu).ffEquiv_algebraMap a

#print axioms model
#print axioms model_integral
#print axioms model_proper
#print axioms model_smooth
#print axioms functionFieldEquiv
#print axioms functionFieldEquiv_constants
end FourCorner.OppositeSchemeModel
