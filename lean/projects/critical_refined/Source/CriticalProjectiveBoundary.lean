import CriticalProjectiveResidues

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalProjectiveBoundary
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation CriticalProjectiveResidues
variable {k:Type*} [Field k]

lemma pole_zero_residue (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational) (ha:v.ord (a k i)<0) :
    evaluate v hv (poleZero i hi h2 v ha)=0 := by
  apply (ResidueValuationFacts.evaluate_zero_iff_ord_pos v hv _
    (inv_ne_zero (CriticalBadUnits.ordered_nonzero i hi h2).1)).mpr
  change 0<v.ord (a k i)⁻¹
  rw [ord_inverse]
  omega

lemma pole_shift_negative (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (ha:v.ord (a k i)<0) :
    v.ord (CriticalBoundaryResidues.shift i)<0 := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hp:v.ord (a k i^2)=2*v.ord (a k i) := by
    simpa only [zpow_ofNat] using v.ord_zpow (a k i) (2:ℤ)
  have hm:v.ord (-1:field k i)=0 := by rw [OddFifthUnramified.ord_neg,v.ord_one]
  have hs:=OddFifthUnramified.ord_add_of_lt v (pow_ne_zero 2 hn.1) (neg_ne_zero.mpr one_ne_zero)
    (by rw [hp,hm];omega)
  have he:v.ord (CriticalBoundaryResidues.shift i)=2*v.ord (a k i) := by
    simpa only [CriticalBoundaryResidues.shift,sub_eq_add_neg,hp] using hs
  omega

/-- The intrinsic original projective b=0 locus is EXACTLY the positive
order locus of a²−1; poles are explicitly retained on their V1 chart. -/
theorem vector_boundary_iff (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational) :
    CriticalElliptic23.Shift (vector i hi h2 v hv)=0 ↔
      0<v.ord (CriticalBoundaryResidues.shift i) := by
  unfold vector
  split_ifs with ha
  · let aa:=regularA i hi h2 v ha
    let t:v.toValuationSubring:=aa^2-1
    have ht:(t:field k i)≠0 := (CriticalBadUnits.ordered_nonzero i hi h2).2.2.2
    have he:=ResidueValuationFacts.evaluate_zero_iff_ord_pos v hv t ht
    change evaluate v hv t=0 ↔ 0<v.ord (CriticalBoundaryResidues.shift i) at he
    have hval:evaluate v hv t=CriticalElliptic23.Shift (finiteVector i hi h2 v hv ha) := by
      simp [t,aa,finiteVector,CriticalElliptic23.Shift,map_sub,map_pow]
    rwa [hval] at he
  · have hn:v.ord (a k i)<0 := by omega
    have hz:=pole_zero_residue i hi h2 v hv hn
    have hs:=pole_shift_negative i hi h2 v hn
    have hnot:¬0<v.ord (CriticalBoundaryResidues.shift i) := by omega
    simp [poleVector,CriticalElliptic23.Shift,hz,hnot]

end FourCorner.CriticalProjectiveBoundary
#print axioms FourCorner.CriticalProjectiveBoundary.pole_zero_residue
#print axioms FourCorner.CriticalProjectiveBoundary.vector_boundary_iff
