import CriticalProjectiveIntegral
import CriticalProjectiveSmooth
import AffineGenericStalk

noncomputable section
namespace FourCorner.CriticalProjectiveField
open AlgebraicGeometry CategoryTheory
open CriticalProj23 CriticalStandardCharts
variable {k : Type*} [Field k]
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def nativeChart (i : k) : Spec (.of (CriticalAffineGeometry.ring i)) ⟶ criticalCurve i :=
  (zeroChartIso i).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι

instance nativeChart_isOpenImmersion (i : k) : IsOpenImmersion (nativeChart i) := by
  unfold nativeChart
  infer_instance

theorem zeroEquiv_coeff (i c : k) :
    zeroEquiv i (algebraMap k (affineRing i 0) c)=algebraMap k (CriticalAffineGeometry.ring i) c := by
  rfl

theorem nativeChart_over_base (i : k) : nativeChart i ≫ criticalToSpec i=
    Spec.map (CommRingCat.ofHom (algebraMap k (CriticalAffineGeometry.ring i))) := by
  change (Spec.map (CommRingCat.ofHom (zeroEquiv i).toRingHom) ≫
    (chartIso i 0).inv ≫ (Proj.basicOpen (criticalGrading i) (coordinate i 0)).ι) ≫ criticalToSpec i = _
  simp only [Category.assoc]
  rw [CriticalChartBase.chart_over_base,←Spec.map_comp,←CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext c
  exact zeroEquiv_coeff i c

/-- The original Proj's ACTUAL generic stalk is identified through its
actual over-k affine open chart. No abstract function-field label replaces it. -/
def fieldEquiv (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    letI := SmoothCurveExtension.fieldAlgebra (criticalToSpec i)
    FractionRing (CriticalAffineGeometry.ring i) ≃ₐ[k] (criticalCurve i).functionField := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  exact AffineGenericStalk.fieldEquiv (criticalToSpec i) (nativeChart i) (nativeChart_over_base i)

theorem generic_diagram (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    letI := CriticalProjectiveIntegral.projective_integral i hi h2
    Spec.map (CommRingCat.ofHom (AffineGenericStalk.ringEquiv (nativeChart i)).toRingHom) ≫
      (criticalCurve i).fromSpecStalk (genericPoint (criticalCurve i)) =
        (Spec (.of (CriticalAffineGeometry.ring i))).fromSpecStalk
          (genericPoint (Spec (.of (CriticalAffineGeometry.ring i)))) ≫ nativeChart i := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  letI := CriticalProjectiveIntegral.projective_integral i hi h2
  exact AffineGenericStalk.generic_diagram (nativeChart i)

end FourCorner.CriticalProjectiveField
#print axioms FourCorner.CriticalProjectiveField.nativeChart_over_base
#print axioms FourCorner.CriticalProjectiveField.fieldEquiv
#print axioms FourCorner.CriticalProjectiveField.generic_diagram
