import HasseInertPole
namespace FourCorner.HasseEvenPoleModel
open HilbertArithmeticHigh11 HasseConicTangentParity

/-- Direct smooth model tangent parity at an even pole when t is a unit. -/
theorem even_pole_model_tangent_even (q : OddPrime)
    (p r u t z w : ℤ_[q.val])
    (hp : PadicInt.toZMod p ≠ 0) (hr : PadicInt.toZMod r = 0)
    (ht : PadicInt.toZMod t ≠ 0)
    (hC : (p-r^2)*u^2-p*t^2+p*(p+r^2)*z^2=0)
    (hDU : (p-r^2)*w^2=2*(p+r^2)*(t^2-2*r^2*z^2))
    (hL : (p-r^2)*u*(p*(p+r^2)*(w+2*t+2*r*z))-
      p*t*(-(p+r^2)*((p-r^2)*w+2*p*t+2*r*(p-r^2)*z))+
      p*(p+r^2)*z*(r*(p-r^2)*w-2*r^2*(p+r^2)*z) ≠ 0) :
    Even (Padic.valuation (((p-r^2)*u*(p*(p+r^2)*(w+2*t+2*r*z))-
      p*t*(-(p+r^2)*((p-r^2)*w+2*p*t+2*r*(p-r^2)*z))+
      p*(p+r^2)*z*(r*(p-r^2)*w-2*r^2*(p+r^2)*z) : ℤ_[q.val]) : ℚ_[q.val])) := by
  have htwo : (2 : ZMod q.val) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hh
    exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
  have ha : PadicInt.toZMod (p-r^2) ≠ 0 := by simpa only [map_sub,map_pow,hr,zero_pow (by decide : 2 ≠ 0),sub_zero] using hp
  have hb : PadicInt.toZMod (p+r^2) ≠ 0 := by simpa only [map_add,map_pow,hr,zero_pow (by decide : 2 ≠ 0),add_zero] using hp
  have hw : PadicInt.toZMod (w+2*t) ≠ 0 := by
    intro hh
    have he := congrArg PadicInt.toZMod hDU
    simp only [map_sub,map_add,map_mul,map_pow,map_ofNat,hr,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero] at he
    have hh' : PadicInt.toZMod w= -2*PadicInt.toZMod t := by
      rw [map_add,map_mul,map_ofNat] at hh
      linear_combination hh
    rw [hh'] at he
    have hn : (PadicInt.toZMod p)*2*(PadicInt.toZMod t)^2=0 := by linear_combination he
    exact (mul_ne_zero (mul_ne_zero hp htwo) (pow_ne_zero 2 ht)) hn
  let U := p*(p+r^2)*(w+2*t+2*r*z)
  let T := -(p+r^2)*((p-r^2)*w+2*p*t+2*r*(p-r^2)*z)
  let Z := r*(p-r^2)*w-2*r^2*(p+r^2)*z
  have hU : PadicInt.toZMod U ≠ 0 := by
    dsimp [U]
    simpa only [map_mul,map_add,map_ofNat,hr,mul_zero,zero_mul,add_zero]
      using mul_ne_zero (mul_ne_zero hp hb) hw
  have hQ : (p-r^2)*U^2-p*T^2+p*(p+r^2)*Z^2=0 := by
    dsimp [U,T,Z]
    linear_combination 2*p^2*r^2*(p+r^2)*hDU
  have hh := primitive_conic_tangent_even q (p-r^2) (-p) (p*(p+r^2)) u t z U T Z ha
    (by simpa only [map_neg,neg_ne_zero] using hp)
    (by simpa only [map_mul] using mul_ne_zero hp hb)
    (by linear_combination hC) (by linear_combination hQ) (Or.inr (Or.inl ht)) (Or.inl hU)
    (by intro hh; apply hL; dsimp [U,T,Z] at hh; linear_combination hh)
  simpa only [U,T,Z,sub_eq_add_neg,mul_neg,neg_mul] using hh

/-- The other primitive chart at an even pole has square first coefficient. -/
theorem even_pole_model_square_of_t_nonunit (q : OddPrime)
    (p r u t z : ℤ_[q.val])
    (hp : PadicInt.toZMod p ≠ 0) (hr : PadicInt.toZMod r = 0)
    (ht : PadicInt.toZMod t = 0)
    (hC : (p-r^2)*u^2-p*t^2+p*(p+r^2)*z^2=0)
    (hprim : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod t ≠ 0 ∨ PadicInt.toZMod z ≠ 0) :
    IsSquare ((-(p-r^2) : ℤ_[q.val]) : ℚ_[q.val]) := by
  have he := congrArg PadicInt.toZMod hC
  simp only [map_sub,map_add,map_mul,map_pow,map_zero,hr,ht,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,add_zero] at he
  have hz : PadicInt.toZMod z ≠ 0 := by
    intro hz
    have hu : PadicInt.toZMod u ≠ 0 := hprim.resolve_right (by simp [ht,hz])
    rw [hz,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at he
    exact (mul_ne_zero hp (pow_ne_zero 2 hu)) he
  have heq : (PadicInt.toZMod u)^2= -(PadicInt.toZMod p)*(PadicInt.toZMod z)^2 := by
    have hh : (PadicInt.toZMod p)*((PadicInt.toZMod u)^2+(PadicInt.toZMod p)*(PadicInt.toZMod z)^2)=0 := by linear_combination he
    have hh' := (mul_eq_zero.mp hh).resolve_left hp
    linear_combination hh'
  apply (padicInt_isSquare_coe_iff_residue_unit q.property.2 (-(p-r^2))
    (by simpa only [map_neg,map_sub,map_pow,hr,zero_pow (by decide : 2 ≠ 0),sub_zero,neg_ne_zero] using hp)).mpr
  simp only [map_neg,map_sub,map_pow,hr,zero_pow (by decide : 2 ≠ 0),sub_zero]
  refine ⟨PadicInt.toZMod u/PadicInt.toZMod z, ?_⟩
  field_simp
  linear_combination -heq

#print axioms even_pole_model_square_of_t_nonunit
#print axioms even_pole_model_tangent_even
end FourCorner.HasseEvenPoleModel
