import CriticalNativeFieldIso

noncomputable section
namespace FourCorner.CriticalNativeFieldIso
variable {k : Type*} [Field k]

private theorem transcendental_coordinate (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    Transcendental k (CriticalAffineFieldBridge.coordinate i 0) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  exact (transcendental_algebraMap_iff (R := k) (S := CriticalAffineGeometry.ring i)
    (IsFractionRing.injective (CriticalAffineGeometry.ring i) (sourceField i))).mpr
      (CriticalAffineDomain.coordinate_transcendental i)

theorem fieldEquiv_x (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    fieldEquiv i hi h2 (CriticalEllipticField.x k)=
      CriticalDirectMap.x (algebraMap k (sourceField i) i)
        (CriticalAffineFieldBridge.coordinate i 0) (CriticalAffineFieldBridge.coordinate i 1) (CriticalAffineFieldBridge.coordinate i 2) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  exact CriticalFieldEquivalence.equiv_x i hi h2 _ _ _
    (CriticalAffineFieldBridge.equations i).1 (CriticalAffineFieldBridge.equations i).2
    (transcendental_coordinate i hi h2) (CriticalAffineFieldBridge.generates i)

theorem fieldEquiv_y (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    fieldEquiv i hi h2 (CriticalEllipticField.y k)=
      CriticalDirectMap.y (algebraMap k (sourceField i) i)
        (CriticalAffineFieldBridge.coordinate i 0) (CriticalAffineFieldBridge.coordinate i 1) (CriticalAffineFieldBridge.coordinate i 2) := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  exact CriticalFieldEquivalence.equiv_y i hi h2 _ _ _
    (CriticalAffineFieldBridge.equations i).1 (CriticalAffineFieldBridge.equations i).2
    (transcendental_coordinate i hi h2) (CriticalAffineFieldBridge.generates i)

/-- Every source rational-map denominator is genuinely nonzero in the
actual literal function field. The hypotheses are exactly the paper's. -/
theorem source_denominators (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) :
    letI := CriticalAffineDomain.ring_isDomain i hi h2
    let I := algebraMap k (sourceField i) i
    let a := CriticalAffineFieldBridge.coordinate i 0
    let b := CriticalAffineFieldBridge.coordinate i 1
    let c := CriticalAffineFieldBridge.coordinate i 2
    a-1 ≠ 0 ∧ a^2-1 ≠ 0 ∧
      CriticalConicParameter.denominator I (CriticalConicParameter.parameter a b) ≠ 0 ∧
      CriticalDirectMap.v I a b ≠ 0 ∧ CriticalQuarticCubic.scale I ≠ 0 ∧
      CriticalDirectMap.X I a b c ^2-1 ≠ 0 ∧ (4:sourceField i) ≠ 0 := by
  letI := CriticalAffineDomain.ring_isDomain i hi h2
  let I := algebraMap k (sourceField i) i
  let a := CriticalAffineFieldBridge.coordinate i 0
  let b := CriticalAffineFieldBridge.coordinate i 1
  let c := CriticalAffineFieldBridge.coordinate i 2
  have hiF : I^2 = -1 := by simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k (sourceField i)) hi
  have h2F : (2:sourceField i) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero (algebraMap k (sourceField i))).mpr h2
  have ht : Transcendental k a := transcendental_coordinate i hi h2
  have hs : a^2-1 ≠ 0 := CriticalFieldEquivalence.shift_nonzero ht
  have ha : a ≠ 1 := by intro h; apply hs; rw [h]; ring
  have hB := (CriticalAffineFieldBridge.equations i).1
  have hC := (CriticalAffineFieldBridge.equations i).2
  refine ⟨sub_ne_zero.mpr ha,hs,
    CriticalConicParameter.denominator_nonzero I a b hiF h2F hB ha,
    CriticalConicParameter.shifted_parameter_nonzero I a b hiF h2F hB ha,
    CriticalQuarticCubic.scale_nonzero I hiF h2F,
    CriticalDirectMap.inverse_denominator I a b c hiF h2F hB hC hs,?_⟩
  convert pow_ne_zero 2 h2F using 1 <;> ring

end FourCorner.CriticalNativeFieldIso
#print axioms FourCorner.CriticalNativeFieldIso.fieldEquiv_x
#print axioms FourCorner.CriticalNativeFieldIso.fieldEquiv_y
#print axioms FourCorner.CriticalNativeFieldIso.source_denominators
