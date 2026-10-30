import HasseGoodUnitRow

namespace FourCorner.HasseOddBadModels

open HilbertArithmeticHigh11 HasseConicTangentParity

private theorem two_ne_zero (q : OddPrime) : (2 : ZMod q.val) ≠ 0 := by
  intro hh
  have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hh
  exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)

/-- The anisotropic binary norm has no nonzero residue zero. -/
theorem residue_norm_anisotropic {F : Type*} [Field F] (h2 : ¬ IsSquare (2 : F))
    (x y : F) (h : x^2=2*y^2) : x=0 ∧ y=0 := by
  have hy : y=0 := by
    by_contra hy
    apply h2
    refine ⟨x/y, ?_⟩
    field_simp
    linear_combination -h
  exact ⟨by rw [hy] at h; simpa using h,hy⟩

/-- Exact smooth model at an arbitrary inert positive-b depth. Coordinates
u,t,w have already been divided by the same half-depth r; no contact-depth
hypothesis is present. The original tangent polar is r cubed times this one. -/
theorem positive_b_model_tangent_even (q : OddPrime)
    (p r B u t z w : ℤ_[q.val])
    (h2 : ¬ IsSquare (2 : ZMod q.val))
    (hp : PadicInt.toZMod p = -1) (hr : PadicInt.toZMod r = 0)
    (hB : PadicInt.toZMod B ≠ 0)
    (hb : p+1=r^2*B)
    (hC : (p-1)*u^2-p*t^2+p*B*z^2=0)
    (hDU : (p-1)*w^2=2*B*(r^2*t^2-2*z^2))
    (hprim : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod t ≠ 0 ∨ PadicInt.toZMod z ≠ 0)
    (hL : (p-1)*u*(p*B*(r*w+2*r*t+2*z))-
      p*t*(-B*((p-1)*r*w+2*p*r*t+2*(p-1)*z))+
      p*B*z*((p-1)*w-2*r*B*z) ≠ 0) :
    Even (Padic.valuation (((p-1)*u*(p*B*(r*w+2*r*t+2*z))-
      p*t*(-B*((p-1)*r*w+2*p*r*t+2*(p-1)*z))+
      p*B*z*((p-1)*w-2*r*B*z) : ℤ_[q.val]) : ℚ_[q.val])) := by
  have htwo := two_ne_zero q
  have ha : PadicInt.toZMod (p-1) ≠ 0 := by
    simpa only [map_sub,map_one,hp,show (-1 : ZMod q.val)-1= -2 by ring,neg_ne_zero] using htwo
  have hp0 : PadicInt.toZMod p ≠ 0 := by rw [hp]; exact neg_ne_zero.mpr one_ne_zero
  have hz : PadicInt.toZMod z ≠ 0 := by
    intro hz
    have he := congrArg PadicInt.toZMod hC
    simp only [map_add,map_sub,map_mul,map_pow,map_zero,map_one,hp,hz] at he
    have hn : (PadicInt.toZMod t)^2=2*(PadicInt.toZMod u)^2 := by linear_combination he
    obtain ⟨ht,hu⟩ := residue_norm_anisotropic h2 _ _ hn
    exact hprim.elim (fun h => h hu) (fun h => h.elim (fun h => h ht) (fun h => h hz))
  have hw : PadicInt.toZMod w ≠ 0 := by
    intro hw
    have he := congrArg PadicInt.toZMod hDU
    simp only [map_sub,map_mul,map_pow,map_ofNat,map_one,map_zero,hp,hr,hw] at he
    have he0 : (2 : ZMod q.val)*(PadicInt.toZMod B)*2*(PadicInt.toZMod z)^2=0 := by
      linear_combination he
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero htwo hB) htwo) (pow_ne_zero 2 hz)) he0
  let U := p*B*(r*w+2*r*t+2*z)
  let T := -B*((p-1)*r*w+2*p*r*t+2*(p-1)*z)
  let Z := (p-1)*w-2*r*B*z
  have hZ : PadicInt.toZMod Z ≠ 0 := by
    dsimp [Z]
    simpa only [map_sub,map_mul,map_ofNat,hr,zero_mul,mul_zero,sub_zero] using mul_ne_zero ha hw
  have hQ : (p-1)*U^2-p*T^2+p*B*Z^2=0 := by
    dsimp [U,T,Z]
    linear_combination (B^2*p*r^2+B*p^2-B*p)*hDU - 2*B^2*p*r^2*t^2*hb
  have hh := primitive_conic_tangent_even q (p-1) (-p) (p*B) u t z U T Z ha
    (by simpa only [map_neg,neg_ne_zero] using hp0)
    (by simpa only [map_mul] using mul_ne_zero hp0 hB)
    (by linear_combination hC) (by linear_combination hQ) hprim (Or.inr (Or.inr hZ))
    (by intro hh; apply hL; dsimp [U,T,Z] at hh; linear_combination hh)
  simpa only [U,T,Z,sub_eq_add_neg,mul_neg,neg_mul] using hh

#print axioms residue_norm_anisotropic
#print axioms positive_b_model_tangent_even

end FourCorner.HasseOddBadModels

namespace FourCorner.HasseOddBadModels
open HilbertArithmeticHigh11 HasseConicTangentParity

/-- The smooth integral model at every positive-a prime of even depth.
The weighted anchor remains primitive even at tangent contact of any depth. -/
theorem positive_a_even_model_tangent_even (q : OddPrime)
    (p r A u t z w : ℤ_[q.val])
    (hp : PadicInt.toZMod p = 1) (hr : PadicInt.toZMod r = 0)
    (hA : PadicInt.toZMod A ≠ 0)
    (ha : p-1=r^2*A)
    (hC : A*u^2-p*t^2+p*(p+1)*z^2=0)
    (hDU : A*w^2=2*(p+1)*(t^2-2*z^2))
    (hprim : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod t ≠ 0 ∨ PadicInt.toZMod z ≠ 0)
    (hL : A*u*(p*(p+1)*(w+2*r*t+2*r*z))-
      p*t*(-(p+1)*(r*A*w+2*p*t+2*r^2*A*z))+
      p*(p+1)*z*(r*A*w-2*(p+1)*z) ≠ 0) :
    Even (Padic.valuation ((A*u*(p*(p+1)*(w+2*r*t+2*r*z))-
      p*t*(-(p+1)*(r*A*w+2*p*t+2*r^2*A*z))+
      p*(p+1)*z*(r*A*w-2*(p+1)*z) : ℤ_[q.val]) : ℚ_[q.val])) := by
  have htwo := two_ne_zero q
  have hp0 : PadicInt.toZMod p ≠ 0 := by simpa only [hp] using (one_ne_zero : (1 : ZMod q.val) ≠ 0)
  have hb0 : PadicInt.toZMod (p+1) ≠ 0 := by simpa only [map_add,map_one,hp,one_add_one_eq_two] using htwo
  have htz : PadicInt.toZMod t ≠ 0 ∨ PadicInt.toZMod z ≠ 0 := by
    by_contra hh
    simp only [not_or,not_not] at hh
    have hu : PadicInt.toZMod u ≠ 0 := hprim.resolve_right (by simp [hh.1,hh.2])
    have he := congrArg PadicInt.toZMod hC
    simp only [map_add,map_sub,map_mul,map_pow,map_zero,hh.1,hh.2,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero,add_zero] at he
    exact (mul_ne_zero hA (pow_ne_zero 2 hu)) he
  let U := p*(p+1)*(w+2*r*t+2*r*z)
  let T := -(p+1)*(r*A*w+2*p*t+2*r^2*A*z)
  let Z := r*A*w-2*(p+1)*z
  have hprimA : PadicInt.toZMod U ≠ 0 ∨ PadicInt.toZMod T ≠ 0 ∨ PadicInt.toZMod Z ≠ 0 := by
    rcases htz with ht | hz
    · right; left
      dsimp [T]
      simpa only [map_neg,map_add,map_mul,map_pow,map_ofNat,hr,zero_mul,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add,add_zero,neg_mul,neg_ne_zero]
        using mul_ne_zero hb0 (mul_ne_zero (mul_ne_zero htwo hp0) ht)
    · right; right
      dsimp [Z]
      simpa only [map_sub,map_mul,map_ofNat,hr,zero_mul,zero_sub,neg_ne_zero]
        using mul_ne_zero (mul_ne_zero htwo hb0) hz
  have hQ : A*U^2-p*T^2+p*(p+1)*Z^2=0 := by
    dsimp [U,T,Z]
    linear_combination 2*p^2*(p+1)*hDU +
      (p*(p+1)*(4*A*p*r^2*z^2+4*A*p*r*w*z+A*p*w^2+4*A*r^2*z^2+4*A*r*w*z-4*p^2*t^2-4*p*t^2-4*p*z^2-4*z^2))*ha
  have hh := primitive_conic_tangent_even q A (-p) (p*(p+1)) u t z U T Z hA
    (by simpa only [map_neg,neg_ne_zero] using hp0)
    (by simpa only [map_mul] using mul_ne_zero hp0 hb0)
    (by linear_combination hC) (by linear_combination hQ) hprim hprimA
    (by intro hh; apply hL; dsimp [U,T,Z] at hh; linear_combination hh)
  simpa only [U,T,Z,sub_eq_add_neg,mul_neg,neg_mul] using hh

#print axioms positive_a_even_model_tangent_even
end FourCorner.HasseOddBadModels
