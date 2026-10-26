import CriticalDoubleOriginalMap
import CriticalDoublePointCount
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
universe u
namespace FourCorner.CriticalCoverGenericField

/-- Simultaneous exact source and base field transport preserves the actual
relative finite dimension. Compatibility of the embeddings is explicit. -/
theorem finite_dimensional_transport {F E F' E' : Type u}
    [Field F] [Field E] [Field F'] [Field E'] [Algebra F E] [Algebra F' E']
    [FiniteDimensional F E] (e : F ≃+* F') (g : E ≃+* E')
    (h : ∀ a : F, g (algebraMap F E a)=algebraMap F' E' (e a)) :
    FiniteDimensional F' E' ∧ Module.finrank F' E'=Module.finrank F E := by
  letI : Algebra F E' := (g.toRingHom.comp (algebraMap F E)).toAlgebra
  let eg : E ≃ₐ[F] E' := AlgEquiv.ofRingEquiv (f:=g) (by intro a; rfl)
  let b0 := (Module.finBasis F E).map eg.toLinearEquiv
  let b := b0.mapCoeffs e (by
    intro a x
    simp only [Algebra.smul_def,RingHom.algebraMap_toAlgebra,RingHom.comp_apply]
    exact congrArg (fun z : E' => z*x) (h a).symm)
  have hfinite : FiniteDimensional F' E' := b.finiteDimensional_of_finite
  refine ⟨hfinite,?_⟩
  simpa using Module.finrank_eq_card_basis b

variable {k : Type u} [Field k]
local instance baseConstants (i:k) : Algebra k (CriticalLiteralDouble.base k i) := CriticalLiteralDouble.baseConstants k i
local instance baseModule (i:k) : Module k (CriticalLiteralDouble.base k i) := (baseConstants i).toModule
local instance coverConstants (i:k) : Algebra k (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.targetConstants k i
local instance coverModule (i:k) : Module k (CriticalLiteralDouble.field k i) := (coverConstants i).toModule
local instance relative (i:k) : Algebra (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.relativeAlgebra k i
local instance relativeModule (i:k) : Module (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := (relative i).toModule
local instance tower (i:k) : IsScalarTower k (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) := CriticalLiteralDouble.constants_base_tower k i

/-- The native algebra on the actual two generic stalks, with algebraMap
EXACTLY the already constructed cover pullback tau. -/
@[instance_reducible] def relativeAlgebra (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    Algebra (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact (CriticalDoubleOriginalMap.pullback i hi h2).toRingHom.toAlgebra

/-- Finite-dimensionality and exact degree TWO for the actual original
scheme generic stalks and the actual cover pullback, over ANY base field. -/
theorem actual_generic_degree_two (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    letI := relativeAlgebra i hi h2
    FiniteDimensional (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField ∧
      Module.finrank (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField=2 := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI := relativeAlgebra i hi h2
  let e := CriticalDoubleOriginalMap.baseFieldEquiv i hi h2
  let g := CriticalDoubleModel.fieldEquiv i hi h2
  have hdegree := CriticalDoublePointCount.degree_two k i hi h2
  haveI : FiniteDimensional (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) :=
    Multiquadratic.Tower.finiteDimensional_first (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.radicand k i)
  have hcompat : ∀ a : CriticalLiteralDouble.base k i,
      g (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) a)=
        algebraMap (CriticalProj23.criticalCurve i).functionField
          (EllipticQuarticModel.curve k).functionField (e a) := by
    intro a
    change g (algebraMap (CriticalLiteralDouble.base k i) (CriticalLiteralDouble.field k i) a)=
      (CriticalDoubleOriginalMap.pullback i hi h2) (e a)
    simp only [e,g,CriticalDoubleOriginalMap.pullback,AlgHom.comp_apply,AlgEquiv.symm_apply_apply,
      IsScalarTower.coe_toAlgHom',AlgEquiv.coe_toAlgHom]
  obtain ⟨hfinite,hdegree'⟩ := finite_dimensional_transport e.toRingEquiv g.toRingEquiv hcompat
  exact ⟨hfinite,hdegree'.trans hdegree⟩

/-- The constant-field scalar tower is the actual one induced by tau;
there is no separate chosen embedding of constants. -/
theorem actual_generic_scalar_tower (i:k) (hi:i^2= -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    letI := relativeAlgebra i hi h2
    IsScalarTower k (CriticalProj23.criticalCurve i).functionField (EllipticQuarticModel.curve k).functionField := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  letI := relativeAlgebra i hi h2
  apply IsScalarTower.of_algebraMap_eq
  intro z
  exact ((CriticalDoubleOriginalMap.pullback i hi h2).commutes z).symm

#print axioms finite_dimensional_transport
#print axioms actual_generic_degree_two
#print axioms actual_generic_scalar_tower
end FourCorner.CriticalCoverGenericField
