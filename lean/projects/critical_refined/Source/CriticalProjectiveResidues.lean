import CriticalBoundaryResidues
import CriticalProjectiveCharacter

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace FourCorner.CriticalProjectiveResidues
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation
variable {k:Type*} [Field k]

lemma pole_orders (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:v.ord (a k i)<0) : v.ord (b k i)=v.ord (a k i) ∧ v.ord (c k i)=v.ord (a k i) := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hi0:=CriticalElliptic23.iota_nonzero i hi
  have hm:1-i≠0 := sub_ne_zero.mpr (Ne.symm (CriticalElliptic23.iota_ne_one i hi h2))
  have hp:=CriticalElliptic23.iota_add_one_nonzero i hi h2
  refine ⟨CriticalProductOrders.negative_quadratic_order v i (1-i) (a k i) (b k i)
    hi0 hm hn.1 (b_squared k i) ha,?_⟩
  apply CriticalProductOrders.negative_quadratic_order v (1+i) (-i) (a k i) (c k i)
    hp (neg_ne_zero.mpr hi0) hn.1 _ ha
  rw [c_squared,map_neg]
  ring

lemma ord_inverse (i:k) (v:Place k (field k i)) : v.ord (a k i)⁻¹= -v.ord (a k i) := by
  simpa only [zpow_neg_one,neg_one_mul] using v.ord_zpow (a k i) (-1:ℤ)

def regularA (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:0≤v.ord (a k i)) : v.toValuationSubring :=
  ⟨a k i,(v.mem_iff_ord_nonneg (CriticalBadUnits.ordered_nonzero i hi h2).1).mpr ha⟩
def regularB (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:0≤v.ord (a k i)) : v.toValuationSubring :=
  ⟨b k i,(v.mem_iff_ord_nonneg (CriticalBadUnits.ordered_nonzero i hi h2).2.1).mpr
    (CriticalProductValuation.integral_of_nonnegative i v hi h2 ha).1⟩
def regularC (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:0≤v.ord (a k i)) : v.toValuationSubring :=
  ⟨c k i,(v.mem_iff_ord_nonneg (CriticalBadUnits.ordered_nonzero i hi h2).2.2.1).mpr
    (CriticalProductValuation.integral_of_nonnegative i v hi h2 ha).2.1⟩

def poleZero (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:v.ord (a k i)<0) : v.toValuationSubring :=
  ⟨(a k i)⁻¹,(v.mem_iff_ord_nonneg (inv_ne_zero (CriticalBadUnits.ordered_nonzero i hi h2).1)).mpr
    (by rw [ord_inverse];omega)⟩
def poleB (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:v.ord (a k i)<0) : v.toValuationSubring :=
  ⟨b k i/a k i,(v.mem_iff_ord_nonneg (div_ne_zero
    (CriticalBadUnits.ordered_nonzero i hi h2).2.1 (CriticalBadUnits.ordered_nonzero i hi h2).1)).mpr
    (by rw [QuadraticRescaledUnit.ord_div _ (CriticalBadUnits.ordered_nonzero i hi h2).2.1
      (CriticalBadUnits.ordered_nonzero i hi h2).1,(pole_orders i hi h2 v ha).1];omega)⟩
def poleC (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (ha:v.ord (a k i)<0) : v.toValuationSubring :=
  ⟨c k i/a k i,(v.mem_iff_ord_nonneg (div_ne_zero
    (CriticalBadUnits.ordered_nonzero i hi h2).2.2.1 (CriticalBadUnits.ordered_nonzero i hi h2).1)).mpr
    (by rw [QuadraticRescaledUnit.ord_div _ (CriticalBadUnits.ordered_nonzero i hi h2).2.2.1
      (CriticalBadUnits.ordered_nonzero i hi h2).1,(pole_orders i hi h2 v ha).2];omega)⟩

def finiteVector (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (hv:v.IsRational) (ha:0≤v.ord (a k i)) : Fin 4→k :=
  ![1,evaluate v hv (regularA i hi h2 v ha),evaluate v hv (regularB i hi h2 v ha),
    evaluate v hv (regularC i hi h2 v ha)]
def poleVector (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (hv:v.IsRational) (ha:v.ord (a k i)<0) : Fin 4→k :=
  ![evaluate v hv (poleZero i hi h2 v ha),1,evaluate v hv (poleB i hi h2 v ha),
    evaluate v hv (poleC i hi h2 v ha)]

/-- The representative is taken from the SAME original field coordinates:
V0=1 on the finite chart, V1=1 at every original V0 pole. -/
def vector (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (hv:v.IsRational) : Fin 4→k :=
  if ha:0≤v.ord (a k i) then finiteVector i hi h2 v hv ha else poleVector i hi h2 v hv (by omega)

lemma finite_critical (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (hv:v.IsRational) (ha:0≤v.ord (a k i)) : CriticalElliptic23.CriticalCoordinates i (finiteVector i hi h2 v hv ha) := by
  let aa:=regularA i hi h2 v ha
  let bb:=regularB i hi h2 v ha
  let cc:=regularC i hi h2 v ha
  have hb:bb^2-1=algebraMap k v.toValuationSubring i*(aa^2-1) := by
    apply Subtype.ext
    exact (actual_critical_equations k i).1
  have hc:cc^2-1=algebraMap k v.toValuationSubring (1+i)*(aa^2-1) := by
    apply Subtype.ext
    exact (actual_critical_equations k i).2
  have hbv:=congrArg (evaluate v hv) hb
  have hcv:=congrArg (evaluate v hv) hc
  simp only [map_sub,map_pow,map_one,map_mul,evaluate_constant] at hbv hcv
  simpa [finiteVector,CriticalElliptic23.CriticalCoordinates,CriticalElliptic23.Shift,aa,bb,cc] using And.intro hbv hcv

lemma pole_critical (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (hv:v.IsRational) (ha:v.ord (a k i)<0) : CriticalElliptic23.CriticalCoordinates i (poleVector i hi h2 v hv ha) := by
  let zz:=poleZero i hi h2 v ha
  let bb:=poleB i hi h2 v ha
  let cc:=poleC i hi h2 v ha
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hq:=actual_critical_equations k i
  have hb:bb^2-zz^2=algebraMap k v.toValuationSubring i*(1-zz^2) := by
    apply Subtype.ext
    change (b k i/a k i)^2-((a k i)⁻¹)^2=algebraMap k (field k i) i*(1-((a k i)⁻¹)^2)
    field_simp [hn.1]
    linear_combination hq.1
  have hc:cc^2-zz^2=algebraMap k v.toValuationSubring (1+i)*(1-zz^2) := by
    apply Subtype.ext
    change (c k i/a k i)^2-((a k i)⁻¹)^2=algebraMap k (field k i) (1+i)*(1-((a k i)⁻¹)^2)
    field_simp [hn.1]
    linear_combination hq.2
  have hbv:=congrArg (evaluate v hv) hb
  have hcv:=congrArg (evaluate v hv) hc
  simp only [map_sub,map_pow,map_one,map_mul,evaluate_constant] at hbv hcv
  simpa [poleVector,CriticalElliptic23.CriticalCoordinates,CriticalElliptic23.Shift,zz,bb,cc] using And.intro hbv hcv

theorem vector_critical (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (hv:v.IsRational) : CriticalElliptic23.CriticalCoordinates i (vector i hi h2 v hv) := by
  unfold vector
  split_ifs with ha
  · exact finite_critical i hi h2 v hv ha
  · exact pole_critical i hi h2 v hv (by omega)

theorem vector_nonzero (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (v:Place k (field k i))
    (hv:v.IsRational) : vector i hi h2 v hv≠0 := by
  intro h
  unfold vector at h
  split_ifs at h with ha
  · have hh:=congrFun h 0
    exact (one_ne_zero : (1:k)≠0) (by simpa [finiteVector] using hh)
  · have hh:=congrFun h 1
    exact (one_ne_zero : (1:k)≠0) (by simpa [poleVector] using hh)

end FourCorner.CriticalProjectiveResidues
#print axioms FourCorner.CriticalProjectiveResidues.pole_orders
#print axioms FourCorner.CriticalProjectiveResidues.vector_critical
#print axioms FourCorner.CriticalProjectiveResidues.vector_nonzero
