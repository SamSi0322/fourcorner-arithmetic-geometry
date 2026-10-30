import CriticalDoubleGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
open AlgebraicGeometry CategoryTheory AlgebraicCurve
universe u
namespace FourCorner.CriticalNormalizationDiagram
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

/-- Nonzero original chart denominators rescale the actual primitive root;
they preserve the whole literal extension, not merely its square equation. -/
theorem normalized_root_generates (i:k) (q:CriticalLiteralDouble.base k i) (hq:q≠0) :
 Algebra.adjoin (CriticalLiteralDouble.base k i)
 {CriticalLiteralDouble.root k i / algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) q}=⊤ :=
 QuadraticRescaledUnit.adjoin_div_algebraMap_eq_top (CriticalLiteralDouble.root k i) hq
 (CriticalLiteralDouble.root_generates k i)

/-- The native cover pullback is the original relative embedding, under the
FIXED coordinate-preserving comparisons of BOTH actual function fields. -/
theorem field_diagram (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
 letI:=CriticalAffineDomain.ring_isDomain i hi h2
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=EllipticQuarticModel.integral k
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
 (CriticalDoubleOriginalMap.pullback i hi h2).toRingHom.comp
 (CriticalDoubleOriginalMap.baseFieldEquiv i hi h2).toRingHom=
 (CriticalDoubleModel.fieldEquiv i hi h2).toRingHom.comp
 (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)) := by
 letI:=CriticalAffineDomain.ring_isDomain i hi h2
 letI:=CriticalProjectiveIntegral.projective_integral i hi h2
 letI:=EllipticQuarticModel.integral k
 letI:=SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
 letI:=SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
 ext z
 change (CriticalDoubleOriginalMap.pullback i hi h2) ((CriticalDoubleOriginalMap.baseFieldEquiv i hi h2) z)=
   (CriticalDoubleModel.fieldEquiv i hi h2) (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) z)
 simp only [CriticalDoubleOriginalMap.pullback,AlgHom.comp_apply,AlgEquiv.symm_apply_apply,
 IsScalarTower.coe_toAlgHom',AlgEquiv.coe_toAlgHom]

end FourCorner.CriticalNormalizationDiagram
#print axioms FourCorner.CriticalNormalizationDiagram.normalized_root_generates
#print axioms FourCorner.CriticalNormalizationDiagram.field_diagram
