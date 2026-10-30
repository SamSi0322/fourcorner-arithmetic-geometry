import CriticalProjectiveField
import CriticalNativeFieldCoordinates
import EllipticQuarticFunctionField
import EllipticQuarticSmooth

noncomputable section
namespace FourCorner.CriticalSchemeIso
open AlgebraicGeometry CategoryTheory
variable {k : Type*} [Field k]
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

/-- The actual generic-stalk k-algebra equivalence of the original
projective Ci and the independently constructed projective E. -/
def genericFieldEquiv (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    (EllipticQuarticModel.curve k).functionField ≃ₐ[k] (CriticalProj23.criticalCurve i).functionField := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
  letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
  exact (EllipticQuarticModel.nativeFieldEquiv k).symm.trans
    ((CriticalNativeFieldIso.fieldEquiv i hi h2).trans (CriticalProjectiveField.fieldEquiv i hi h2))

/-- A genuine k-scheme isomorphism of the ORIGINAL literal Proj with the
independent smooth projective closure of y²=x³−x. All discarded rational
formula denominators are restored by actual proper smooth-curve extension. -/
theorem exists_iso (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := EllipticQuarticModel.integral k
    letI := SmoothCurveExtension.fieldAlgebra (CriticalProj23.criticalToSpec i)
    letI := SmoothCurveExtension.fieldAlgebra (EllipticQuarticModel.toBase k)
    ∃ f : CriticalProj23.criticalCurve i ≅ EllipticQuarticModel.curve k,
      f.hom ≫ EllipticQuarticModel.toBase k=CriticalProj23.criticalToSpec i ∧
      (CriticalProj23.criticalCurve i).fromSpecStalk (genericPoint (CriticalProj23.criticalCurve i)) ≫ f.hom=
        Spec.map (CommRingCat.ofHom (genericFieldEquiv i hi h2).toRingEquiv.toRingHom) ≫
          (EllipticQuarticModel.curve k).fromSpecStalk (genericPoint (EllipticQuarticModel.curve k)) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  letI := EllipticQuarticModel.integral k
  letI := CriticalProjectiveSmooth.projective_smooth i hi h2
  letI := CriticalProj23.criticalToSpec_isProper i
  letI := EllipticQuarticModel.smooth k h2
  letI := EllipticQuarticModel.proper k
  exact SmoothCurveExtension.iso_of_functionField_algEquiv
    (CriticalProj23.criticalToSpec i) (EllipticQuarticModel.toBase k) (genericFieldEquiv i hi h2)

def iso (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    CriticalProj23.criticalCurve i ≅ EllipticQuarticModel.curve k :=
  Classical.choose (exists_iso i hi h2)

theorem iso_over_base (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    (iso i hi h2).hom ≫ EllipticQuarticModel.toBase k=CriticalProj23.criticalToSpec i :=
  (Classical.choose_spec (exists_iso i hi h2)).1

end FourCorner.CriticalSchemeIso
#print axioms FourCorner.CriticalSchemeIso.genericFieldEquiv
#print axioms FourCorner.CriticalSchemeIso.exists_iso
#print axioms FourCorner.CriticalSchemeIso.iso
#print axioms FourCorner.CriticalSchemeIso.iso_over_base
