import CriticalDoubleCM
import CriticalDirectMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace FourCorner.CriticalProductSquareclass
open CriticalConicParameter CriticalQuarticCubic
variable {k : Type*} [Field k]

def ellipticX (i u c : k) : k :=
  ((-c*denominator i u+(1+i)+2*(u-i))/(u-i)^2-i)/(1-i)
def squareFactor (i u c : k) : k :=
  -i*(u-i)*(c*denominator i u-u^2+(2-2*i)*u+i)/((u-1)*denominator i u)

/-- Exact polynomial certificate for the original product squareclass.
This uses the literal conic and last original quadric, not an abstract cover. -/
theorem cleared_identity (i u c : k) (hi : i^2 = -1)
    (hc : c^2*denominator i u^2 = denominator i u^2+
      (1+i)*((u^2-2*u+i)^2-denominator i u^2)) :
    2*(1-i)*(u-1)^2*(c*denominator i u^2+
      (u^2-2*u+i)*(-u^2+2*i*u-i)) =
    i^2*(-c*denominator i u+(1+i)+2*(u-i)-i*(u-i)^2)*
      (c*denominator i u-u^2+(2-2*i)*u+i)^2 := by
  have h3 : i^3 = -i := by rw [pow_succ,hi]; ring
  have h4 : i^4 = 1 := by rw [pow_succ,h3]; linear_combination -hi
  have h5 : i^5 = i := by rw [pow_succ,h4,one_mul]
  have h6 : i^6 = -1 := by rw [pow_succ,h5]; simpa only [pow_two] using hi
  have h7 : i^7 = -i := by rw [pow_succ,h6]; ring
  dsimp [denominator] at hc ⊢
  linear_combination (norm := ring_nf)
    (-c*u^2+i*c+(2-i)*u^2+(-4+4*i)*u+1-2*i)*hc
  simp only [hi,h3,h4,h5,h6,h7]
  ring

/-- On the original conic parameter chart the normalized radicand is
exactly elliptic x times the square of the displayed rational function. -/
theorem product_squareclass (i u c : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hd : denominator i u≠0) (hu : u-i≠0) (hu1 : u-1≠0)
    (hc : c^2-1=(1+i)*(first i u^2-1)) :
    2*(c+first i u*second i u)=ellipticX i u c*squareFactor i u c^2 := by
  have hs : (1-i)≠0 := scale_nonzero i hi h2
  have hC : c^2*denominator i u^2=denominator i u^2+
      (1+i)*((u^2-2*u+i)^2-denominator i u^2) := by
    dsimp [first] at hc
    field_simp [hd] at hc
    linear_combination hc
  have hh:=cleared_identity i u c hi hC
  dsimp [ellipticX,squareFactor,first,second]
  field_simp [hd,hu,hu1,hs]
  linear_combination hh


theorem parameter_ne_one (i a b : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hb : b^2-1=i*(a^2-1)) (hs : a^2-1≠0) : parameter a b-1≠0 := by
  have ha : a≠1 := by intro h; apply hs; rw [h]; ring
  intro hu
  have he : parameter a b=1 := sub_eq_zero.mp hu
  have hba : b=a := by
    dsimp [parameter] at he
    have := (div_eq_iff (sub_ne_zero.mpr ha)).mp he
    linear_combination this
  rw [hba] at hb
  have hm : 1-i≠0 := scale_nonzero i hi h2
  exact (mul_ne_zero hm hs) (by linear_combination hb)

/-- The squareclass comparison is on the original ordered Ci coordinates,
using exactly the accepted direct native E map, with one common parameter. -/
theorem original_product_squareclass (i a b c : k) (hi : i^2 = -1) (h2 : (2:k)≠0)
    (hb : b^2-1=i*(a^2-1)) (hc : c^2-1=(1+i)*(a^2-1))
    (hs : a^2-1≠0) :
    2*(c+a*b)=CriticalDirectMap.x i a b c*squareFactor i (parameter a b) c^2 := by
  have ha : a≠1 := by intro h; apply hs; rw [h]; ring
  have h:=product_squareclass i (parameter a b) c hi h2
    (denominator_nonzero i a b hi h2 hb ha)
    (shifted_parameter_nonzero i a b hi h2 hb ha)
    (parameter_ne_one i a b hi h2 hb hs)
    (by rw [first_inverse i a b hi h2 hb ha];exact hc)
  rw [first_inverse i a b hi h2 hb ha,second_inverse i a b hi h2 hb ha] at h
  exact h

end FourCorner.CriticalProductSquareclass
#print axioms FourCorner.CriticalProductSquareclass.cleared_identity
#print axioms FourCorner.CriticalProductSquareclass.product_squareclass

#print axioms FourCorner.CriticalProductSquareclass.parameter_ne_one
#print axioms FourCorner.CriticalProductSquareclass.original_product_squareclass
