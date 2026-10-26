import CriticalDoubleModel
import CriticalOriginalFieldCoordinates
import CriticalProjectiveField

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 40000
open AlgebraicGeometry CategoryTheory
universe u
namespace FourCorner.CriticalDoubleOriginalMap
variable {k:Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

/-- The literal original (a,b,c) field is the actual generic stalk of Ci,
via its actual V0 affine chart, preserving the three ordered coordinates. -/
def baseFieldEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    CriticalLiteralDouble.base k i ≃ₐ[k] (CriticalProj23.criticalCurve i).functionField := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  exact (CriticalOriginalFieldCoordinates.affineEquiv k i hi h2).trans
    (CriticalProjectiveField.fieldEquiv i hi h2)

/-- Pullback on actual generic stalks is exactly the specified original base
inclusion into the literal product-root field, with both proved comparisons. -/
def pullback (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    (CriticalProj23.criticalCurve i).functionField →ₐ[k] (EllipticQuarticModel.curve k).functionField := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact (CriticalDoubleModel.fieldEquiv i hi h2).toAlgHom.comp
    ((IsScalarTower.toAlgHom k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i)).comp
      (baseFieldEquiv i hi h2).symm.toAlgHom)

/-- A genuine over-k proper-curve map representing the EXACT original
normalized product extension. The full generic diagram is retained. -/
theorem exists_original_cover_map (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    ∃ π:EllipticQuarticModel.curve k ⟶ CriticalProj23.criticalCurve i,
      π ≫ CriticalProj23.criticalToSpec i=EllipticQuarticModel.toBase k ∧
      (EllipticQuarticModel.curve k).fromSpecStalk (genericPoint (EllipticQuarticModel.curve k)) ≫ π=
        Spec.map (CommRingCat.ofHom (pullback i hi h2).toRingHom) ≫
          (CriticalProj23.criticalCurve i).fromSpecStalk (genericPoint (CriticalProj23.criticalCurve i)) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := EllipticQuarticModel.smooth k h2
  letI := CriticalProj23.criticalToSpec_isProper i
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  apply SmoothCurveExtension.extend_generic (EllipticQuarticModel.toBase k) (CriticalProj23.criticalToSpec i)
    (Spec.map (CommRingCat.ofHom (pullback i hi h2).toRingHom) ≫
      (CriticalProj23.criticalCurve i).fromSpecStalk (genericPoint (CriticalProj23.criticalCurve i)))
  simp only [Category.assoc,SmoothCurveExtension.generic_comp_to_base]
  rw [←Spec.map_comp,←CommRingCat.ofHom_comp]
  congr 1
  ext z
  exact (pullback i hi h2).commutes z


def map (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    EllipticQuarticModel.curve k ⟶ CriticalProj23.criticalCurve i := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact Classical.choose (exists_original_cover_map i hi h2)

theorem map_over_base (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    map i hi h2 ≫ CriticalProj23.criticalToSpec i=EllipticQuarticModel.toBase k := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact (Classical.choose_spec (exists_original_cover_map i hi h2)).1

theorem map_proper (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) : IsProper (map i hi h2) := by
  letI := CriticalProj23.criticalToSpec_isProper i
  letI : IsProper (map i hi h2 ≫ CriticalProj23.criticalToSpec i) := by
    rw [map_over_base i hi h2]
    exact EllipticQuarticModel.proper k
  exact IsProper.of_comp (map i hi h2) (CriticalProj23.criticalToSpec i)

theorem map_generic (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    (EllipticQuarticModel.curve k).fromSpecStalk (genericPoint (EllipticQuarticModel.curve k)) ≫ map i hi h2=
      Spec.map (CommRingCat.ofHom (pullback i hi h2).toRingHom) ≫
        (CriticalProj23.criticalCurve i).fromSpecStalk (genericPoint (CriticalProj23.criticalCurve i)) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact (Classical.choose_spec (exists_original_cover_map i hi h2)).2

end FourCorner.CriticalDoubleOriginalMap
#print axioms FourCorner.CriticalDoubleOriginalMap.baseFieldEquiv
#print axioms FourCorner.CriticalDoubleOriginalMap.pullback
#print axioms FourCorner.CriticalDoubleOriginalMap.exists_original_cover_map

#print axioms FourCorner.CriticalDoubleOriginalMap.map_over_base
#print axioms FourCorner.CriticalDoubleOriginalMap.map_proper
#print axioms FourCorner.CriticalDoubleOriginalMap.map_generic
