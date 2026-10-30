import CriticalCoverGenericField

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
universe u
namespace FourCorner.CriticalCoverGenericField
variable {k : Type u} [Field k]
attribute [local instance] baseConstants baseModule coverConstants coverModule relative relativeModule tower

/-- The actual generic-stalk extension induced by the fixed original scheme
cover is separable over ANY original field, via its exact field comparisons. -/
theorem actual_generic_separable (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    letI := relativeAlgebra i hi h2
    Algebra.IsSeparable (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI := relativeAlgebra i hi h2
  letI := CriticalLiteralDouble.separable k i h2
  let e := CriticalDoubleOriginalMap.baseFieldEquiv i hi h2
  let g := CriticalDoubleModel.fieldEquiv i hi h2
  apply Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv g.toRingEquiv
  ext a
  symm
  change g (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) a)=
    (CriticalDoubleOriginalMap.pullback i hi h2) (e a)
  simp only [e,g,CriticalDoubleOriginalMap.pullback,AlgHom.comp_apply,AlgEquiv.symm_apply_apply,
    IsScalarTower.coe_toAlgHom',AlgEquiv.coe_toAlgHom]

#print axioms actual_generic_separable
end FourCorner.CriticalCoverGenericField
