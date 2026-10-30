import CriticalAffineDomain
import CriticalAffineFieldBridge
import CriticalFieldInverse

noncomputable section
namespace FourCorner.CriticalNativeFieldIso
variable {k : Type*} [Field k]

/-- The ACTUAL literal V0 affine function field, with its proved domain
instance. The parameter i and all original equations are unchanged. -/
abbrev sourceField (i : k) := FractionRing (CriticalAffineGeometry.ring i)

/-- Genuine k-field isomorphism between the native y²=x³−x function field
and the function field of the ORIGINAL two-quadric V0 affine quotient.
There is no genus, field-comparison, CharZero or perfectness assumption. -/
def fieldEquiv (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    CriticalEllipticField.field k ≃ₐ[k] sourceField i := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  have ht : Transcendental k (CriticalAffineFieldBridge.coordinate i 0) :=
    (transcendental_algebraMap_iff (R := k) (S := CriticalAffineGeometry.ring i)
      (IsFractionRing.injective (CriticalAffineGeometry.ring i) (sourceField i))).mpr
        (CriticalAffineDomain.coordinate_transcendental i)
  exact CriticalAffineFieldBridge.equiv i hi h2 ht

/-- All three ORIGINAL quotient-coordinate generators are exactly the
explicit inverse elliptic formulas under the genuine field isomorphism. -/
theorem original_coordinates (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    let f := fieldEquiv i hi h2
    (f.symm (CriticalAffineFieldBridge.coordinate i 0)=
      CriticalDirectMap.inverseA (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k)) ∧
    (f.symm (CriticalAffineFieldBridge.coordinate i 1)=
      CriticalDirectMap.inverseB (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k)) ∧
    (f.symm (CriticalAffineFieldBridge.coordinate i 2)=
      CriticalDirectMap.inverseC (algebraMap k (CriticalEllipticField.field k) i) (CriticalEllipticField.x k) (CriticalEllipticField.y k)) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  have ht : Transcendental k (CriticalAffineFieldBridge.coordinate i 0) :=
    (transcendental_algebraMap_iff (R := k) (S := CriticalAffineGeometry.ring i)
      (IsFractionRing.injective (CriticalAffineGeometry.ring i) (sourceField i))).mpr
        (CriticalAffineDomain.coordinate_transcendental i)
  exact CriticalFieldEquivalence.inverse_coordinates i hi h2
    (CriticalAffineFieldBridge.coordinate i 0) (CriticalAffineFieldBridge.coordinate i 1) (CriticalAffineFieldBridge.coordinate i 2)
    (CriticalAffineFieldBridge.equations i).1 (CriticalAffineFieldBridge.equations i).2 ht (CriticalAffineFieldBridge.generates i)

end FourCorner.CriticalNativeFieldIso
#print axioms FourCorner.CriticalNativeFieldIso.fieldEquiv
#print axioms FourCorner.CriticalNativeFieldIso.original_coordinates
