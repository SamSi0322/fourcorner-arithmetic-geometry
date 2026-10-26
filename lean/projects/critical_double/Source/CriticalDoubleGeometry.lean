import CriticalNativeGeometricGenus
import CriticalCoverNativeEtale
import CriticalSchemePointPlaces
import CriticalSignPoints

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalDoubleGeometry
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule

/-- On EVERY original chart with nonzero denominator q, the SAME literal
root extension has the normalized equation S_q²=2f/q². -/
theorem normalized_root_square (i:k) (q:CriticalLiteralDouble.base k i) :
 (CriticalLiteralDouble.root k i / algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) q)^2=
 algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)
   (CriticalLiteralDouble.radicand k i / q^2) := by
 rw [div_pow,CriticalLiteralDouble.root_square,map_div₀,map_pow]

theorem rational_points (i:k) :
 Nonempty (CriticalSchemePointPlaces.BasePoints i) ∧
 Nonempty (CriticalSchemePointPlaces.CoverPoints (k:=k)) :=
 ⟨⟨⟨CriticalSignPoints.point i (fun _=>false),CriticalSignPoints.point_over i _⟩⟩,
 ⟨⟨CriticalDoubleModel.rationalPoint,CriticalDoubleModel.rationalPoint_over⟩⟩⟩

/-- Native smooth proper integral geometrically connected curves, with
actual rational points and an actual finite etale map. No perfectness,
characteristic-zero or algebraic-closure premise occurs. -/
theorem geometric_cover (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 IsIntegral (CriticalProj23.criticalCurve i) ∧
 IsIntegral (EllipticQuarticModel.curve k) ∧
 SmoothOfRelativeDimension 1 (CriticalProj23.criticalToSpec i) ∧
 SmoothOfRelativeDimension 1 (EllipticQuarticModel.toBase k) ∧
 IsProper (CriticalProj23.criticalToSpec i) ∧
 IsProper (EllipticQuarticModel.toBase k) ∧
 GeometricallyConnected (CriticalProj23.criticalToSpec i) ∧
 GeometricallyConnected (EllipticQuarticModel.toBase k) ∧
 IsFinite (CriticalDoubleOriginalMap.map i hi h2) ∧
 Etale (CriticalDoubleOriginalMap.map i hi h2) ∧
 Nonempty (CriticalSchemePointPlaces.BasePoints i) ∧
 Nonempty (CriticalSchemePointPlaces.CoverPoints (k:=k)) := by
 letI:=CriticalAffineDomain.ring_isDomain i hi h2
 exact ⟨CriticalProjectiveIntegral.projective_integral i hi h2,
 EllipticQuarticModel.integral k,CriticalProjectiveSmooth.projective_smooth i hi h2,
 EllipticQuarticModel.smooth k h2,CriticalProj23.criticalToSpec_isProper i,
 EllipticQuarticModel.proper k,CriticalGeometricConnected.geometricallyConnected i hi h2,
 CriticalDoubleModel.geometricallyConnected i hi h2,
 (CriticalCoverNativeProperties.actual_finite_etale i hi h2).1,
 (CriticalCoverNativeProperties.actual_finite_etale i hi h2).2,rational_points i⟩

/-- The native generic stalk extension of this SAME Scheme map has degree
TWO. The relative algebra is explicitly its pullback, not a new field map. -/
theorem degree_two (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 letI:=CriticalAffineDomain.ring_isDomain i hi h2
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=EllipticQuarticModel.integral k
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
 letI:=CriticalCoverGenericField.relativeAlgebra i hi h2
 FiniteDimensional (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField ∧
 Module.finrank (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField=2 :=
 CriticalCoverGenericField.actual_generic_degree_two i hi h2

end FourCorner.CriticalDoubleGeometry
#print axioms FourCorner.CriticalDoubleGeometry.normalized_root_square
#print axioms FourCorner.CriticalDoubleGeometry.rational_points
#print axioms FourCorner.CriticalDoubleGeometry.geometric_cover
#print axioms FourCorner.CriticalDoubleGeometry.degree_two
