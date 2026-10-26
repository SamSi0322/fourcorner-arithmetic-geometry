import CriticalLiteralDouble
import ResidueValuationFacts
import CriticalSignPoints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalBoundaryResidues
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation
variable {k : Type*} [Field k]

def shift (i:k) : field k i := a k i^2-1

lemma unit_of_shift {F:Type*} [Field F] [Algebra k F]
    (v:Place k F) (A:k) (t r:F) (hA:A≠0) (ht:t≠0)
    (he:r^2=1+algebraMap k F A*t) (ho:0<v.ord t) : v.ord r=0 := by
  have hA0:algebraMap k F A≠0 := (_root_.map_ne_zero _).mpr hA
  have hAt:v.ord (algebraMap k F A*t)=v.ord t := by rw [v.ord_mul hA0 ht,v.ord_algebraMap,zero_add]
  have hs:=OddFifthUnramified.ord_add_of_lt v one_ne_zero (mul_ne_zero hA0 ht)
    (by rw [v.ord_one,hAt];exact ho)
  have hr:=v.ord_zpow r (2:ℤ)
  rw [zpow_ofNat,he,hs,v.ord_one] at hr
  omega

/-- At EVERY actual original boundary place the V0-chart coordinates are
units. Their genuine residue values are the three signs of the paper. -/
theorem coordinate_orders (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hp:0<v.ord (shift i)) :
    v.ord (a k i)=0 ∧ v.ord (b k i)=0 ∧ v.ord (c k i)=0 := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hq:=actual_critical_equations k i
  refine ⟨unit_of_shift v 1 (shift i) (a k i) one_ne_zero hn.2.2.2 ?_ hp,
    unit_of_shift v i (shift i) (b k i) (CriticalElliptic23.iota_nonzero i hi) hn.2.2.2 ?_ hp,
    unit_of_shift v (1+i) (shift i) (c k i) (CriticalElliptic23.iota_add_one_nonzero i hi h2) hn.2.2.2 ?_ hp⟩
  · simp [shift]
  · dsimp [shift]
    linear_combination hq.1
  · dsimp [shift]
    simp only [map_add,map_one] at hq ⊢
    linear_combination hq.2

def A (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hp:0<v.ord (shift i)) : v.toValuationSubring :=
  ⟨a k i,(v.mem_iff_ord_nonneg (CriticalBadUnits.ordered_nonzero i hi h2).1).mpr
    (by rw [(coordinate_orders i hi h2 v hp).1])⟩
def B (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hp:0<v.ord (shift i)) : v.toValuationSubring :=
  ⟨b k i,(v.mem_iff_ord_nonneg (CriticalBadUnits.ordered_nonzero i hi h2).2.1).mpr
    (by rw [(coordinate_orders i hi h2 v hp).2.1])⟩
def C (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hp:0<v.ord (shift i)) : v.toValuationSubring :=
  ⟨c k i,(v.mem_iff_ord_nonneg (CriticalBadUnits.ordered_nonzero i hi h2).2.2.1).mpr
    (by rw [(coordinate_orders i hi h2 v hp).2.2])⟩

theorem residue_squares (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational) (hp:0<v.ord (shift i)) :
    evaluate v hv (A i hi h2 v hp)^2=1 ∧
    evaluate v hv (B i hi h2 v hp)^2=1 ∧
    evaluate v hv (C i hi h2 v hp)^2=1 := by
  let aa:=A i hi h2 v hp
  let bb:=B i hi h2 v hp
  let cc:=C i hi h2 v hp
  let t:=aa^2-1
  have ht:(t:field k i)=shift i := rfl
  have ht0:evaluate v hv t=0 :=
    (ResidueValuationFacts.evaluate_zero_iff_ord_pos v hv t
      (CriticalBadUnits.ordered_nonzero i hi h2).2.2.2).mpr hp
  have hb:bb^2-1=algebraMap k v.toValuationSubring i*t := by
    apply Subtype.ext
    exact (actual_critical_equations k i).1
  have hc:cc^2-1=algebraMap k v.toValuationSubring (1+i)*t := by
    apply Subtype.ext
    change c k i^2-1=algebraMap k (field k i) (1+i)*(a k i^2-1)
    exact (actual_critical_equations k i).2
  have hab:=congrArg (evaluate v hv) hb
  have hac:=congrArg (evaluate v hv) hc
  simp only [map_sub,map_pow,map_one,map_mul,evaluate_constant,ht0,mul_zero,sub_eq_zero] at hab hac
  have haa:=congrArg (evaluate v hv) (show aa^2-1=t from rfl)
  simp only [map_sub,map_pow,map_one,ht0,sub_eq_zero] at haa
  exact ⟨haa,hab,hac⟩

/-- The literal normalized root used at every zero-product boundary place. -/
theorem normalized_root_square (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    (CriticalLiteralDouble.root k i /
      algebraMap (field k i) (CriticalLiteralDouble.field k i) (shift i))^2 =
    algebraMap (field k i) (CriticalLiteralDouble.field k i)
      (-2*algebraMap k (field k i) i / CriticalProductValuation.f' i) := by
  have hs:shift i≠0 := (CriticalBadUnits.ordered_nonzero i hi h2).2.2.2
  have hf:CriticalProductValuation.f' i≠0 := (CriticalProductValuation.nonzero i hi h2).2
  rw [div_pow,CriticalLiteralDouble.root_square,←map_pow,←map_div₀]
  congr 1
  apply (div_eq_div_iff (pow_ne_zero 2 hs) hf).mpr
  have he:=CriticalProductValuation.product_identity i
  change 2*CriticalProductValuation.f i*CriticalProductValuation.f' i = _
  dsimp [shift]
  linear_combination 2*he

theorem normalized_root_generates (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    Algebra.adjoin (field k i) {CriticalLiteralDouble.root k i /
      algebraMap (field k i) (CriticalLiteralDouble.field k i) (shift i)}=⊤ :=
  QuadraticRescaledUnit.adjoin_div_algebraMap_eq_top (CriticalLiteralDouble.root k i)
    (CriticalBadUnits.ordered_nonzero i hi h2).2.2.2 (CriticalLiteralDouble.root_generates k i)

end FourCorner.CriticalBoundaryResidues
#print axioms FourCorner.CriticalBoundaryResidues.coordinate_orders
#print axioms FourCorner.CriticalBoundaryResidues.residue_squares
#print axioms FourCorner.CriticalBoundaryResidues.normalized_root_square
#print axioms FourCorner.CriticalBoundaryResidues.normalized_root_generates
