import CriticalDoubleGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalDoubleFullGeometry
variable {k:Type u} [Field k]

/-- All geometric assertions refer to the fixed original Ci scheme and the
fixed smooth proper model of its literal S²=2(c+ab) field extension. -/
def Geometry (i:k) (hi:i^2= -1) (h2:(2:k)≠0) : Prop :=
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
 Nonempty (CriticalSchemePointPlaces.CoverPoints (k:=k))

def DegreeTwo (i:k) (hi:i^2= -1) (h2:(2:k)≠0) : Prop :=
 letI:=CriticalAffineDomain.ring_isDomain i hi h2
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=EllipticQuarticModel.integral k
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
 letI:=CriticalCoverGenericField.relativeAlgebra i hi h2
 FiniteDimensional (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField ∧
 Module.finrank (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField=2

/-- Genus of the actual native function fields after every algebraically
closed constant extension, retaining every original base field k. -/
def GeometricGenusOne (i:k) (hi:i^2= -1) (h2:(2:k)≠0) : Prop :=
 ∀ (L:Type u) [Field L] [Algebra k L] [IsAlgClosed L],
 letI:=EllipticQuarticModel.integral k
 letI:=CriticalAffineDomain.ring_isDomain i hi h2
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 letI:=CriticalNativeGeometricGenus.cover_domain L i hi h2
 letI:=CriticalNativeGeometricGenus.base_domain L i hi h2
 genusFF L (FractionRing (L⊗[k](EllipticQuarticModel.curve k).functionField))=1 ∧
 genusFF L (FractionRing (L⊗[k](CriticalProj23.criticalCurve i).functionField))=1

theorem geometry (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 Geometry i hi h2 ∧ DegreeTwo i hi h2 ∧ GeometricGenusOne i hi h2 := by
 refine ⟨CriticalDoubleGeometry.geometric_cover i hi h2,
 CriticalDoubleGeometry.degree_two i hi h2,?_⟩
 intro L _ _ _
 exact ⟨CriticalNativeGeometricGenus.cover_genus_one L i hi h2,
 CriticalNativeGeometricGenus.base_genus_one L i hi h2⟩

end FourCorner.CriticalDoubleFullGeometry
#print axioms FourCorner.CriticalDoubleFullGeometry.geometry
