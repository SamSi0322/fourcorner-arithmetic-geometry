import HasseDyadicDepthFive

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace FourCorner.HasseDyadicUnitFinite

def mod4 : ZMod 32 →+* ZMod 4 := ZMod.castHom (by decide) _
def mod16 : ZMod 32 →+* ZMod 16 := ZMod.castHom (by decide) _
def mod8 : ZMod 32 →+* ZMod 8 := ZMod.castHom (by decide) _
def odd32 (x : ZMod 32) : Prop := x.val % 2=1
private instance (x : ZMod 32) : Decidable (odd32 x) := inferInstanceAs (Decidable (x.val%2=1))

private theorem unitOne_product_square : ∀ (s t : ZMod 32),
    odd32 t → mod4 s=0 →
      (2*t^2-1-s^2)*((1+s^2)*(2*t^2-1))=1 := by decide

private theorem square_one_sign : ∀ u : ZMod 32,
    u^2=1 → mod4 u=1 → mod16 u=1 := by decide

/-- The exact positive-sign normalized unit product in the unit-one source
model, using only its literal square equations modulo 32. -/
theorem unitOne_product_residue (s x y t : ZMod 32)
    (ht : odd32 t) (hs : mod4 s=0)
    (hx : x^2=2*t^2-1-s^2) (hy : y^2=(1+s^2)*(2*t^2-1))
    (hxy : mod4 (x*y)=1) : mod16 (x*y)=1 := by
  apply square_one_sign
  · rw [mul_pow,hx,hy]
    exact unitOne_product_square s t ht hs
  · exact hxy

private theorem unitOne_H_residue : ∀ (x y t s : ZMod 16),
    x*y=1 → t.val%2=1 →
      (x*y+(4*s)*(2*t+1)*(x+y)+2*t^2-1)=2+8*s := by decide

/-- The residue computation producing the exceptional depth-five bit.
The factor s=4S retains whether v₂(s)=2 or v₂(s)>2. -/
theorem unitOne_tangent_numerator (S x y t : ZMod 32)
    (ht : odd32 t)
    (hx : x^2=2*t^2-1-(4*S)^2)
    (hy : y^2=(1+(4*S)^2)*(2*t^2-1))
    (hxy : mod4 (x*y)=1) :
    mod16 (x*y+(4*S)*(2*t+1)*(x+y)+
      2*(1+2*(4*S)^2)*t^2+2*(4*S)^2*t-(1+(4*S)^2))=2+8*mod16 S := by
  have hs : mod4 (4*S)=0 := by
    simp only [map_mul,map_ofNat]
    have hf : ∀ u : ZMod 4, 4*u=0 := by decide
    exact hf _
  have hprod := unitOne_product_residue (4*S) x y t ht hs hx hy hxy
  have ht16 : (mod16 t).val%2=1 := by
    change (t.val%16)%2=1
    change t.val%2=1 at ht
    omega
  have hsq : (4*mod16 S)^2=0 := by
    have hf : ∀ u : ZMod 16, (4*u)^2=0 := by decide
    exact hf _
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_one] at hprod ⊢
  rw [hsq]
  norm_num only [mul_zero,zero_mul,zero_add,add_zero,one_mul,zero_pow] at ⊢
  exact unitOne_H_residue _ _ _ _ hprod ht16

#print axioms unitOne_product_residue
#print axioms unitOne_tangent_numerator
end FourCorner.HasseDyadicUnitFinite
