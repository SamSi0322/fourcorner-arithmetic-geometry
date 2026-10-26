import HasseOddSymbol
import FourCorner.CommonRootPadicResidue

/-! Arithmetic tangent parity on an actual integral smooth diagonal conic.
This supplies the geometric-looking good-prime tangent assertion by an exact
elementary valuation identity; no divisor or Brauer extension is assumed. -/
namespace FourCorner.HasseConicTangentParity

open HilbertArithmeticHigh11

variable {q : ℕ} [Fact q.Prime]

theorem valuation_zero_of_residue_ne_zero (x : ℤ_[q]) (hx : PadicInt.toZMod x ≠ 0) :
    (x : ℚ_[q]).valuation=0 := by
  have hn : ‖(x : ℚ_[q])‖=1 := padicInt_norm_coe_eq_one_of_residue_ne_zero x hx
  have hx0 : (x : ℚ_[q]) ≠ 0 := by
    intro hh
    have hx' : x=0 := PadicInt.coe_eq_zero.mp hh
    exact hx (by simp [hx'])
  by_contra hne
  have hv : 0<(x : ℚ_[q]).valuation :=
    lt_of_le_of_ne x.valuation_coe_nonneg (Ne.symm hne)
  have hlt := (commonRoot_norm_lt_one_iff hx0).mpr hv
  rw [hn] at hlt
  exact lt_irrefl _ hlt

private theorem conic_overlap {F : Type*} [Field F] (a b c x y z X Y Z : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hP : a*x^2+b*y^2+c*z^2=0) (hQ : a*X^2+b*Y^2+c*Z^2=0)
    (hp : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) (hq : X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) :
    (x ≠ 0 ∧ X ≠ 0) ∨ (y ≠ 0 ∧ Y ≠ 0) ∨ (z ≠ 0 ∧ Z ≠ 0) := by
  have hPxy : x=0 → y=0 → z=0 := by
    intro hx hy
    have hh : c*z^2=0 := by simpa only [hx,hy,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add] using hP
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hc)
  have hPxz : x=0 → z=0 → y=0 := by
    intro hx hz
    have hh : b*y^2=0 := by simpa only [hx,hz,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add,add_zero] using hP
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hb)
  have hPyz : y=0 → z=0 → x=0 := by
    intro hy hz
    have hh : a*x^2=0 := by simpa only [hy,hz,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] using hP
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left ha)
  have hQxy : X=0 → Y=0 → Z=0 := by
    intro hx hy
    have hh : c*Z^2=0 := by simpa only [hx,hy,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add] using hQ
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hc)
  have hQxz : X=0 → Z=0 → Y=0 := by
    intro hx hz
    have hh : b*Y^2=0 := by simpa only [hx,hz,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add,add_zero] using hQ
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hb)
  have hQyz : Y=0 → Z=0 → X=0 := by
    intro hy hz
    have hh : a*X^2=0 := by simpa only [hy,hz,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] using hQ
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left ha)
  have hp0 : ¬ (x=0 ∧ y=0 ∧ z=0) := by
    rintro ⟨hx,hy,hz⟩
    exact hp.elim (fun h => h hx) (fun h => h.elim (fun h => h hy) (fun h => h hz))
  have hq0 : ¬ (X=0 ∧ Y=0 ∧ Z=0) := by
    rintro ⟨hx,hy,hz⟩
    exact hq.elim (fun h => h hx) (fun h => h.elim (fun h => h hy) (fun h => h hz))
  by_cases hx : x=0
  · have hy : y ≠ 0 := fun hy => hp0 ⟨hx,hy,hPxy hx hy⟩
    have hz : z ≠ 0 := fun hz => hp0 ⟨hx,hPxz hx hz,hz⟩
    by_cases hY : Y=0
    · have hZ : Z ≠ 0 := fun hZ => hq0 ⟨hQyz hY hZ,hY,hZ⟩
      exact Or.inr (Or.inr ⟨hz,hZ⟩)
    · exact Or.inr (Or.inl ⟨hy,hY⟩)
  · by_cases hX : X=0
    · have hY : Y ≠ 0 := fun hY => hq0 ⟨hX,hY,hQxy hX hY⟩
      have hZ : Z ≠ 0 := fun hZ => hq0 ⟨hX,hQxz hX hZ,hZ⟩
      by_cases hy : y=0
      · have hz : z ≠ 0 := fun hz => hx (hPyz hy hz)
        exact Or.inr (Or.inr ⟨hz,hZ⟩)
      · exact Or.inr (Or.inl ⟨hy,hY⟩)
    · exact Or.inl ⟨hx,hX⟩

private theorem tangent_even_x (q : OddPrime) (a b c x y z X Y Z : ℤ_[q.val])
    (ha : PadicInt.toZMod a ≠ 0) (hb : PadicInt.toZMod b ≠ 0) (hc : PadicInt.toZMod c ≠ 0)
    (hx : PadicInt.toZMod x ≠ 0) (hX : PadicInt.toZMod X ≠ 0)
    (hP : a*x^2+b*y^2+c*z^2=0) (hQ : a*X^2+b*Y^2+c*Z^2=0)
    (hL : a*x*X+b*y*Y+c*z*Z ≠ 0) :
    Even (((a*x*X+b*y*Y+c*z*Z : ℤ_[q.val]) : ℚ_[q.val]).valuation) := by
  let l := a*x*X+b*y*Y+c*z*Z
  by_cases hr : PadicInt.toZMod l ≠ 0
  · rw [valuation_zero_of_residue_ne_zero l hr]
    exact ⟨0,by simp⟩
  have hr0 : PadicInt.toZMod l=0 := not_ne_iff.mp hr
  let m := l-2*a*x*X
  have htwo : (2 : ZMod q.val) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hh
    exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
  have hmres : PadicInt.toZMod m ≠ 0 := by
    dsimp [m]
    rw [map_sub,map_mul,map_mul,map_mul,map_ofNat,hr0,zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero htwo ha) hx) hX)
  have hm : (m : ℚ_[q.val]) ≠ 0 := by
    intro hh
    have hh' : m=0 := PadicInt.coe_eq_zero.mp hh
    exact hmres (by simp [hh'])
  have hl : (l : ℚ_[q.val]) ≠ 0 := fun hh => hL (PadicInt.coe_eq_zero.mp hh)
  have hid : l*m= -(b*c)*(y*Z-z*Y)^2 := by
    dsimp [l,m]
    linear_combination -(a*X^2)*hP+(b*y^2+c*z^2)*hQ
  have hbc : (b*c : ℤ_[q.val]) ≠ 0 := by
    intro hh
    have hh' := congrArg PadicInt.toZMod hh
    simp only [map_mul,map_zero] at hh'
    exact (mul_ne_zero hb hc) hh'
  have hd : ((y*Z-z*Y : ℤ_[q.val]) : ℚ_[q.val]) ≠ 0 := by
    intro hh
    have hh' : y*Z-z*Y=0 := PadicInt.coe_eq_zero.mp hh
    rw [hh',zero_pow (by decide : 2 ≠ 0),mul_zero] at hid
    have hh'' : (l : ℚ_[q.val])*(m : ℚ_[q.val])=0 := by
      simpa only [PadicInt.coe_mul,PadicInt.coe_zero] using
        congrArg (fun u : ℤ_[q.val] => (u : ℚ_[q.val])) hid
    exact (mul_ne_zero hl hm) hh''
  have hh : (l : ℚ_[q.val])*(m : ℚ_[q.val]) =
      -((b*c : ℤ_[q.val]) : ℚ_[q.val])*(((y*Z-z*Y : ℤ_[q.val]) : ℚ_[q.val]))^2 := by
    simpa only [PadicInt.coe_mul,PadicInt.coe_neg,PadicInt.coe_pow] using
      congrArg (fun u : ℤ_[q.val] => (u : ℚ_[q.val])) hid
  have hv := congrArg Padic.valuation hh
  rw [Padic.valuation_mul hl hm,valuation_zero_of_residue_ne_zero m hmres,add_zero,
    Padic.valuation_mul (neg_ne_zero.mpr (PadicInt.coe_ne_zero.mpr hbc)) (pow_ne_zero _ hd),
    commonRoot_val_neg,PadicInt.coe_mul,Padic.valuation_mul
      (PadicInt.coe_ne_zero.mpr (show b ≠ 0 from fun hh => hb (by simp [hh])))
      (PadicInt.coe_ne_zero.mpr (show c ≠ 0 from fun hh => hc (by simp [hh]))),
    valuation_zero_of_residue_ne_zero b hb,valuation_zero_of_residue_ne_zero c hc,
    zero_add,zero_add,Padic.valuation_pow] at hv
  exact ⟨((y*Z-z*Y : ℤ_[q.val]) : ℚ_[q.val]).valuation,by simpa only [Nat.cast_ofNat,two_mul] using hv⟩

/-- Every nonzero tangent value on a smooth integral diagonal conic at an
odd prime has even valuation, for any two primitive integral points.
This includes reduction to the tangent point and every positive depth. -/
theorem primitive_conic_tangent_even (q : OddPrime) (a b c x y z X Y Z : ℤ_[q.val])
    (ha : PadicInt.toZMod a ≠ 0) (hb : PadicInt.toZMod b ≠ 0) (hc : PadicInt.toZMod c ≠ 0)
    (hP : a*x^2+b*y^2+c*z^2=0) (hQ : a*X^2+b*Y^2+c*Z^2=0)
    (hp : PadicInt.toZMod x ≠ 0 ∨ PadicInt.toZMod y ≠ 0 ∨ PadicInt.toZMod z ≠ 0)
    (hq : PadicInt.toZMod X ≠ 0 ∨ PadicInt.toZMod Y ≠ 0 ∨ PadicInt.toZMod Z ≠ 0)
    (hL : a*x*X+b*y*Y+c*z*Z ≠ 0) :
    Even (((a*x*X+b*y*Y+c*z*Z : ℤ_[q.val]) : ℚ_[q.val]).valuation) := by
  have hp' := congrArg PadicInt.toZMod hP
  have hq' := congrArg PadicInt.toZMod hQ
  simp only [map_add,map_mul,map_pow,map_zero] at hp' hq'
  rcases conic_overlap _ _ _ _ _ _ _ _ _ ha hb hc hp' hq' hp hq with h | h | h
  · exact tangent_even_x q a b c x y z X Y Z ha hb hc h.1 h.2 hP hQ hL
  · have hh := tangent_even_x q b a c y x z Y X Z hb ha hc h.1 h.2
      (by linear_combination hP) (by linear_combination hQ)
      (by intro hh; apply hL; linear_combination hh)
    simpa only [add_comm,add_left_comm,add_assoc] using hh

  · have hh := tangent_even_x q c b a z y x Z Y X hc hb ha h.1 h.2
      (by linear_combination hP) (by linear_combination hQ)
      (by intro hh; apply hL; linear_combination hh)
    simpa only [add_comm,add_left_comm,add_assoc] using hh

private theorem anchor_kernel_zero {F : Type*} [Field F] (p z w t : F)
    (h2 : (2 : F) ≠ 0) (hp : p ≠ 0) (hb : p+1 ≠ 0)
    (hz : (p-1)*w-2*(p+1)*z=0)
    (hu : p*(p+1)*(w+2*t+2*z)=0)
    (ht : -(p+1)*((p-1)*w+2*p*t+2*(p-1)*z)=0) : z=0 ∧ t=0 ∧ w=0 := by
  have hu' := (mul_eq_zero.mp hu).resolve_left (mul_ne_zero hp hb)
  have ht' := (mul_eq_zero.mp ht).resolve_left (neg_ne_zero.mpr hb)
  have hzt : 2*z+t=0 := by
    apply (mul_eq_zero.mp (show (2*p)*(2*z+t)=0 by
      linear_combination ht'-hz)).resolve_left (mul_ne_zero h2 hp)
  have hwz : w=2*z := by linear_combination hu'-2*hzt
  have hz0 : z=0 := by
    have hh : (2*2 : F)*z=0 := by linear_combination -hz+(p-1)*hwz
    exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero h2 h2)
  exact ⟨hz0,by linear_combination hzt-2*hz0,by linear_combination hwz+2*hz0⟩

/-- The actual manuscript anchor is primitive over every smooth odd-prime
integral model. This is the missing vertical-divisor input in elementary form. -/
theorem integral_source_tangent_even (q : OddPrime) (p z u w t : ℤ_[q.val])
    (hp : PadicInt.toZMod p ≠ 0) (ha : PadicInt.toZMod (p-1) ≠ 0)
    (hb : PadicInt.toZMod (p+1) ≠ 0)
    (hDU : (p-1)*w^2=2*(p+1)*(t^2-2*z^2))
    (hC : (p-1)*u^2-p*t^2+p*(p+1)*z^2=0)
    (hprim : PadicInt.toZMod z ≠ 0 ∨ PadicInt.toZMod t ≠ 0 ∨ PadicInt.toZMod w ≠ 0)
    (hL : (p-1)*(p*(p+1)*(w+2*t+2*z))*u-
      p*(-(p+1)*((p-1)*w+2*p*t+2*(p-1)*z))*t+
      p*(p+1)*((p-1)*w-2*(p+1)*z)*z ≠ 0) :
    Even (Padic.valuation (((p-1)*(p*(p+1)*(w+2*t+2*z))*u-
      p*(-(p+1)*((p-1)*w+2*p*t+2*(p-1)*z))*t+
      p*(p+1)*((p-1)*w-2*(p+1)*z)*z : ℤ_[q.val]) : ℚ_[q.val])) := by
  let z1 := (p-1)*w-2*(p+1)*z
  let u1 := p*(p+1)*(w+2*t+2*z)
  let t1 := -(p+1)*((p-1)*w+2*p*t+2*(p-1)*z)
  have hanc : (p-1)*u1^2-p*t1^2+p*(p+1)*z1^2=0 := by
    dsimp [z1,u1,t1]
    linear_combination 2*p^2*(p+1)*hDU
  have hprimC : PadicInt.toZMod u ≠ 0 ∨ PadicInt.toZMod t ≠ 0 ∨ PadicInt.toZMod z ≠ 0 := by
    by_cases hz : PadicInt.toZMod z ≠ 0
    · exact Or.inr (Or.inr hz)
    by_cases ht : PadicInt.toZMod t ≠ 0
    · exact Or.inr (Or.inl ht)
    have hz0 := not_ne_iff.mp hz
    have ht0 := not_ne_iff.mp ht
    have hw : PadicInt.toZMod w ≠ 0 := hprim.resolve_left hz |>.resolve_left ht
    have hh := congrArg PadicInt.toZMod hDU
    simp only [map_mul,map_pow,map_sub,hz0,ht0,zero_pow (by decide : 2 ≠ 0),mul_zero,sub_zero] at hh
    exact False.elim ((mul_ne_zero ha (pow_ne_zero 2 hw)) (by simpa only [map_sub] using hh))
  have hprimA : PadicInt.toZMod u1 ≠ 0 ∨ PadicInt.toZMod t1 ≠ 0 ∨ PadicInt.toZMod z1 ≠ 0 := by
    by_contra hh
    simp only [not_or,not_not] at hh
    have h2 : (2 : ZMod q.val) ≠ 0 := by
      intro hh
      have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hh
      exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
    have hz1 := hh.2.2
    have hu1 := hh.1
    have ht1 := hh.2.1
    dsimp [z1] at hz1
    dsimp [u1] at hu1
    dsimp [t1] at ht1
    simp only [map_add,map_sub,map_mul,map_ofNat,map_neg,map_one] at hz1 hu1 ht1
    have hb' : PadicInt.toZMod p+1 ≠ 0 := by simpa only [map_add,map_one] using hb
    obtain ⟨hz,ht,hw⟩ := anchor_kernel_zero _ _ _ _ h2 hp hb' hz1 hu1 ht1
    exact hprim.elim (fun h => h hz) (fun h => h.elim (fun h => h ht) (fun h => h hw))
  have hh := primitive_conic_tangent_even q (p-1) (-p) (p*(p+1)) u t z u1 t1 z1
    ha (by simpa only [map_neg,neg_ne_zero] using hp)
    (by simpa only [map_mul] using mul_ne_zero hp hb)
    (by linear_combination hC) (by linear_combination hanc) hprimC hprimA
    (by intro hh; apply hL; dsimp [u1,t1,z1] at hh; linear_combination hh)
  have heq : (p-1)*u*u1+(-p)*t*t1+p*(p+1)*z*z1=
      (p-1)*(p*(p+1)*(w+2*t+2*z))*u-
      p*(-(p+1)*((p-1)*w+2*p*t+2*(p-1)*z))*t+
      p*(p+1)*((p-1)*w-2*(p+1)*z)*z := by
    dsimp [u1,t1,z1]
    ring
  rw [heq] at hh
  exact hh

#print axioms valuation_zero_of_residue_ne_zero
#print axioms tangent_even_x
#print axioms primitive_conic_tangent_even
#print axioms integral_source_tangent_even

end FourCorner.HasseConicTangentParity
