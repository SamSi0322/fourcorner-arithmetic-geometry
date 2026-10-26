import CriticalOriginalFieldEquiv
import CriticalNativeFieldIso

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalOriginalFieldCoordinates
open CriticalRadicalField
variable (k:Type*) [Field k]

def affineEquiv (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    field k i ≃ₐ[k] CriticalNativeFieldIso.sourceField i := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  exact (CriticalOriginalFieldEquiv.equiv k i hi h2).symm.trans
    (CriticalNativeFieldIso.fieldEquiv i hi h2)

/-- The new radical/affine comparison preserves every ORIGINAL ordered
coordinate, so the subsequent proper-curve comparison has no hidden automorphism. -/
theorem coordinates (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    affineEquiv k i hi h2 (a k i)=CriticalAffineFieldBridge.coordinate i 0 ∧
    affineEquiv k i hi h2 (b k i)=CriticalAffineFieldBridge.coordinate i 1 ∧
    affineEquiv k i hi h2 (c k i)=CriticalAffineFieldBridge.coordinate i 2 := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  have hq:=actual_critical_equations k i
  have ho:=CriticalFieldEquivalence.inverse_coordinates i hi h2 (a k i) (b k i) (c k i)
    hq.1 (by simpa only [map_add,map_one] using hq.2)
    (a_transcendental k i) (CriticalOriginalFieldEquiv.original_generate k i)
  have hn:=CriticalNativeFieldIso.original_coordinates i hi h2
  change (CriticalOriginalFieldEquiv.equiv k i hi h2).symm (a k i)=_ ∧
    (CriticalOriginalFieldEquiv.equiv k i hi h2).symm (b k i)=_ ∧
    (CriticalOriginalFieldEquiv.equiv k i hi h2).symm (c k i)=_ at ho
  constructor
  · change (CriticalNativeFieldIso.fieldEquiv i hi h2)
      ((CriticalOriginalFieldEquiv.equiv k i hi h2).symm (a k i))=_
    rw [ho.1,←hn.1]
    exact (CriticalNativeFieldIso.fieldEquiv i hi h2).apply_symm_apply _
  constructor
  · change (CriticalNativeFieldIso.fieldEquiv i hi h2)
      ((CriticalOriginalFieldEquiv.equiv k i hi h2).symm (b k i))=_
    rw [ho.2.1,←hn.2.1]
    exact (CriticalNativeFieldIso.fieldEquiv i hi h2).apply_symm_apply _
  · change (CriticalNativeFieldIso.fieldEquiv i hi h2)
      ((CriticalOriginalFieldEquiv.equiv k i hi h2).symm (c k i))=_
    rw [ho.2.2,←hn.2.2]
    exact (CriticalNativeFieldIso.fieldEquiv i hi h2).apply_symm_apply _

end FourCorner.CriticalOriginalFieldCoordinates
#print axioms FourCorner.CriticalOriginalFieldCoordinates.affineEquiv
#print axioms FourCorner.CriticalOriginalFieldCoordinates.coordinates
