import CriticalCoverGenericSeparable
import RestrictionUnramifiedTransport
import CriticalProjectiveSmooth

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry AlgebraicCurve
universe u
namespace FourCorner.CriticalCoverNativeProperties
variable {k : Type u} [Field k]
attribute [local instance] CriticalCoverGenericField.baseConstants CriticalCoverGenericField.baseModule
 CriticalCoverGenericField.coverConstants CriticalCoverGenericField.coverModule
 CriticalCoverGenericField.relative CriticalCoverGenericField.relativeModule CriticalCoverGenericField.tower

/-- Formal unramifiedness at every actual native valuation-ring restriction.
The literal quadratic result is transported through the two proved original
function-field comparisons and their exact inclusion diagram. -/
theorem actual_place_unramified (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    letI := CriticalCoverGenericField.relativeAlgebra i hi h2
    letI := (CriticalCoverGenericField.actual_generic_degree_two i hi h2).1
    letI := CriticalCoverGenericField.actual_generic_scalar_tower i hi h2
    ∀ w : Place k (EllipticQuarticModel.curve k).functionField,
      (Place.restrictInclusion (CriticalProj23.criticalCurve i).functionField w).FormallyUnramified := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI := CriticalCoverGenericField.relativeAlgebra i hi h2
  letI := (CriticalCoverGenericField.actual_generic_degree_two i hi h2).1
  letI := CriticalCoverGenericField.actual_generic_scalar_tower i hi h2
  letI : NeZero (2:k) := ⟨h2⟩
  letI := CriticalLiteralDouble.separable k i h2
  letI : FiniteDimensional (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) :=
    Multiquadratic.Tower.finiteDimensional_first (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.radicand k i)
  let e := CriticalDoubleOriginalMap.baseFieldEquiv i hi h2
  let g := CriticalDoubleModel.fieldEquiv i hi h2
  have hc : ∀ a : CriticalLiteralDouble.base k i,
      g (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) a)=
        algebraMap (CriticalProj23.criticalCurve i).functionField
          (EllipticQuarticModel.curve k).functionField (e a) := by
    intro a
    change g (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) a)=
      (CriticalDoubleOriginalMap.pullback i hi h2) (e a)
    simp only [e,g,CriticalDoubleOriginalMap.pullback,AlgHom.comp_apply,AlgEquiv.symm_apply_apply,
      IsScalarTower.coe_toAlgHom',AlgEquiv.coe_toAlgHom]
  apply RestrictionUnramifiedTransport.all_restrictions e g hc
  intro w
  exact PlaceDifferentUnramified.restriction_formallyUnramified w
    (CriticalLiteralDouble.unramified k i hi h2 w).1

/-- Native finiteness and formal unramifiedness of the fixed ORIGINAL
critical double map, over every field with i^2=-1 and 2 nonzero. The stalk
argument includes the generic point and every closed residue degree. -/
theorem actual_finite_unramified (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    IsFinite (CriticalDoubleOriginalMap.map i hi h2) ∧
      FormallyUnramified (CriticalDoubleOriginalMap.map i hi h2) ∧
      LocallyOfFiniteType (CriticalDoubleOriginalMap.map i hi h2) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := EllipticQuarticModel.smooth k h2
  letI := CriticalProjectiveSmooth.projective_smooth i hi h2
  letI := EllipticQuarticModel.proper k
  letI := CriticalProj23.criticalToSpec_isProper i
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI := CriticalCoverGenericField.relativeAlgebra i hi h2
  letI := (CriticalCoverGenericField.actual_generic_degree_two i hi h2).1
  letI := CriticalCoverGenericField.actual_generic_scalar_tower i hi h2
  letI := CriticalCoverGenericField.actual_generic_separable i hi h2
  have hτ : (algebraMap (CriticalProj23.criticalCurve i).functionField
      (EllipticQuarticModel.curve k).functionField).FormallyUnramified := by
    apply RingHom.formallyUnramified_algebraMap.mpr
    exact Algebra.FormallyUnramified.of_isSeparable _ _
  exact AllPointSchemeProperties.finite_and_unramified
    (EllipticQuarticModel.toBase k) (CriticalProj23.criticalToSpec i)
    (CriticalCoverGenericField.actual_generic_scalar_tower i hi h2)
    (CriticalDoubleOriginalMap.map i hi h2) (CriticalDoubleOriginalMap.map_over_base i hi h2)
    (CriticalDoubleOriginalMap.map_generic i hi h2) hτ (actual_place_unramified i hi h2)

#print axioms actual_place_unramified
#print axioms actual_finite_unramified
end FourCorner.CriticalCoverNativeProperties
