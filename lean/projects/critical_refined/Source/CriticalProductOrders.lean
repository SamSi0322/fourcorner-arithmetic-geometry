import CriticalProductValuation

noncomputable section
namespace FourCorner.CriticalProductOrders
open AlgebraicCurve CriticalRadicalField CriticalProductValuation
open OddFifthUnramified
variable {k : Type*} [Field k]
set_option maxHeartbeats 1500000

lemma negative_quadratic_order {F:Type*} [Field F] [Algebra k F]
    (w:Place k F) (A D:k) (z r:F) (hA:A≠0) (hD:D≠0) (hz:z≠0)
    (he:r^2=algebraMap k F A*z^2+algebraMap k F D) (hv:w.ord z<0) :
    w.ord r=w.ord z := by
  have ha : algebraMap k F A≠0 := (map_ne_zero _).mpr hA
  have hd : algebraMap k F D≠0 := (map_ne_zero _).mpr hD
  have hzsq : w.ord (z^2)=2*w.ord z := by simpa only [zpow_ofNat] using w.ord_zpow z (2:ℤ)
  have hrsq : w.ord (r^2)=2*w.ord r := by simpa only [zpow_ofNat] using w.ord_zpow r (2:ℤ)
  have hx : w.ord (algebraMap k F A*z^2)=2*w.ord z := by
    rw [w.ord_mul ha (pow_ne_zero _ hz),w.ord_algebraMap,hzsq,zero_add]
  have hsum := ord_add_of_lt w (mul_ne_zero ha (pow_ne_zero _ hz)) hd
    (by rw [hx,w.ord_algebraMap];omega)
  have e := congrArg w.ord he
  rw [hrsq,hsum,hx] at e
  omega

theorem negative_a (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (w:Place k (field k i)) (ha:w.ord (a k i)<0) :
    w.ord (f i)=2*w.ord (a k i) := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hi0:=CriticalElliptic23.iota_nonzero i hi
  have hp:=CriticalElliptic23.iota_add_one_nonzero i hi h2
  have hm : 1-i≠0 := sub_ne_zero.mpr (Ne.symm (CriticalElliptic23.iota_ne_one i hi h2))
  have hb:=negative_quadratic_order w i (1-i) (a k i) (b k i) hi0 hm hn.1
    (b_squared k i) ha
  have hcform : c k i^2=algebraMap k (field k i) (1+i)*a k i^2+
      algebraMap k (field k i) (-i) := by rw [c_squared,map_neg];ring
  have hc:=negative_quadratic_order w (1+i) (-i) (a k i) (c k i) hp
    (neg_ne_zero.mpr hi0) hn.1 hcform ha
  have hab : w.ord (a k i*b k i)=2*w.ord (a k i) := by
    rw [w.ord_mul hn.1 hn.2.1,hb];ring
  have hsum := ord_add_of_lt w (mul_ne_zero hn.1 hn.2.1) hn.2.2.1
    (by rw [hab,hc];omega)
  simpa only [f,add_comm,hab] using hsum

theorem positive_c (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (w:Place k (field k i)) (hc:0<w.ord (c k i)) : w.ord (f i)=0 := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hi0:=CriticalElliptic23.iota_nonzero i hi
  have hp:=CriticalElliptic23.iota_add_one_nonzero i hi h2
  have hiN : algebraMap k (field k i) i≠0 := (map_ne_zero _).mpr hi0
  have hpN : algebraMap k (field k i) (1+i)≠0 := (map_ne_zero _).mpr hp
  have eA : algebraMap k (field k i) (1+i)*a k i^2=
      algebraMap k (field k i) i+c k i^2 := by linear_combination -(c_squared k i)
  have hc2:=square_order i w (c k i)
  have oA := ord_add_of_lt w hiN (pow_ne_zero 2 hn.2.2.1)
    (by rw [w.ord_algebraMap,hc2];omega)
  have ha0 : w.ord (a k i)=0 := by
    rw [←eA,w.ord_mul hpN (pow_ne_zero 2 hn.1),square_order] at oA
    simp only [w.ord_algebraMap,zero_add] at oA
    omega
  have eB : algebraMap k (field k i) (1+i)*b k i^2=
      1+algebraMap k (field k i) i*c k i^2 := by
    have hb:=b_squared k i
    have hc:=c_squared k i
    simp only [map_add,map_sub,map_one] at hb hc ⊢
    linear_combination (1+algebraMap k (field k i) i)*hb - algebraMap k (field k i) i*hc
  have hmul : w.ord (algebraMap k (field k i) i*c k i^2)=2*w.ord (c k i) := by
    rw [w.ord_mul hiN (pow_ne_zero 2 hn.2.2.1),w.ord_algebraMap,hc2,zero_add]
  have oB := ord_add_of_lt w one_ne_zero (mul_ne_zero hiN (pow_ne_zero 2 hn.2.2.1))
    (by rw [w.ord_one,hmul];omega)
  have hb0 : w.ord (b k i)=0 := by
    rw [←eB,w.ord_mul hpN (pow_ne_zero 2 hn.2.1),w.ord_algebraMap,square_order,w.ord_one] at oB
    omega
  have hab : w.ord (a k i*b k i)=0 := by rw [w.ord_mul hn.1 hn.2.1,ha0,hb0];rfl
  have hsum:=ord_add_of_lt w (mul_ne_zero hn.1 hn.2.1) hn.2.2.1 (by omega)
  simpa only [f,add_comm,hab] using hsum

theorem positive_f_partner_unit (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (w:Place k (field k i)) (ha:0≤w.ord (a k i)) (hf:0<w.ord (f i)) :
    w.ord (f' i)=0 := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hff:=nonzero i hi h2
  have hm:=integral_of_nonnegative i w hi h2 ha
  have hc : w.ord (c k i)=0 := by
    by_contra hz
    have hp : 0<w.ord (c k i) := by omega
    have hzero:=positive_c i hi h2 w hp
    omega
  have h2F : (2:field k i)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k (field k i))).mpr h2
  have h2ord : w.ord (2:field k i)=0 := by
    simpa only [map_ofNat] using w.ord_algebraMap (2:k)
  have hprod : w.ord (2*c k i)=0 := by rw [w.ord_mul h2F hn.2.2.1,h2ord,hc];rfl
  have hsum:=ord_add_of_lt w (mul_ne_zero h2F hn.2.2.1) (neg_ne_zero.mpr hff.1)
    (by rw [ord_neg,hprod];exact hf)
  have eid : 2*c k i + -f i=f' i := by dsimp [f,f'];ring
  rw [eid,hprod] at hsum
  exact hsum

theorem all_places_even (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (w:Place k (field k i)) : Even (w.ord (2*f i)) := by
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hff:=nonzero i hi h2
  have h2F : (2:field k i)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k (field k i))).mpr h2
  have h2ord : w.ord (2:field k i)=0 := by
    simpa only [map_ofNat] using w.ord_algebraMap (2:k)
  rw [w.ord_mul h2F hff.1,h2ord,zero_add]
  by_cases ha : w.ord (a k i)<0
  · rw [negative_a i hi h2 w ha]
    exact ⟨w.ord (a k i),by ring⟩
  · have ha0 : 0≤w.ord (a k i) := by omega
    have hm:=integral_of_nonnegative i w hi h2 ha0
    by_cases hf:w.ord (f i)=0
    · rw [hf];exact ⟨0,by simp⟩
    · have hp:0<w.ord (f i) := by omega
      have ho:=positive_f_partner_unit i hi h2 w ha0 hp
      have hi0:=CriticalElliptic23.iota_nonzero i hi
      have hiF:algebraMap k (field k i) i≠0 := (map_ne_zero _).mpr hi0
      have he:=congrArg w.ord (product_identity i)
      rw [w.ord_mul hff.1 hff.2,ho,add_zero,
        w.ord_mul (neg_ne_zero.mpr hiF) (pow_ne_zero 2 hn.2.2.2),ord_neg,
        w.ord_algebraMap,square_order,zero_add] at he
      exact ⟨w.ord (a k i^2-1),by omega⟩

#print axioms negative_a
#print axioms positive_c
#print axioms positive_f_partner_unit
#print axioms all_places_even
end FourCorner.CriticalProductOrders
