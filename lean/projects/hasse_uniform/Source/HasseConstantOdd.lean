import HasseConstantCorrection

namespace FourCorner.HasseConstantOdd

open HilbertArithmeticHigh11 HasseConstantCorrection HasseHilbertArithmetic
open HilbertWellDefinedHigh11 HasseOddSymbol HasseLocalUnits HasseObstructionArithmetic HasseSignAlgebra

/-- Exact odd formula for the constant correction, at arbitrary positive or
negative valuation depths of p-1. -/
theorem constantSign_odd (q : OddPrime) (p : ℚ) (hp : 1<p) :
    constantSign p hp q.val=(legendreSym q.val (-2))^((padicValRat q.val (p-1) : ZMod 2).val) := by
  have htwo : (-2 : ZMod q.val) ≠ 0 := by
    apply neg_ne_zero.mpr
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hh
    exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
  have hv : ((-2 : ℚ_[q.val]).valuation : ZMod 2)=0 := by
    rw [commonRoot_val_neg,commonRoot_val_two q.property.2]
    rfl
  have hc : (((HasseTangentGlobal.firstCoefficient p : ℚ_[q.val]).valuation) : ZMod 2)=
      (padicValRat q.val (p-1) : ZMod 2) := by
    have he : (HasseTangentGlobal.firstCoefficient p : ℚ_[q.val])= -((p-1 : ℚ) : ℚ_[q.val]) := by
      simp [HasseTangentGlobal.firstCoefficient]
    rw [he,commonRoot_val_neg,Padic.valuation_ratCast]
  rw [constantSign,rationalSign_symm,rationalSign_eq_oddSign]
  change oddSign q (-2 : ℚ_[q.val]) (HasseTangentGlobal.firstCoefficient p : ℚ_[q.val]) _ _= _
  simp only [oddSign,hv,hc,ZMod.val_zero,zero_mul,pow_zero,one_mul,mul_one]
  have hr := residue_intCast (q:=q.val) (-2) (by simpa using htwo)
  have hr' : residue (-2 : ℚ_[q.val]) (by norm_num)=(-2 : ZMod q.val) := by simpa only [Int.cast_neg,Int.cast_ofNat] using hr
  rw [hr']
  simp only [legendreSym,Int.cast_neg,Int.cast_ofNat]

theorem constantSign_odd_even (q : OddPrime) (p : ℚ) (hp : 1<p)
    (he : Even (padicValRat q.val (p-1))) : constantSign p hp q.val=1 := by
  rw [constantSign_odd]
  have hv : (padicValRat q.val (p-1) : ZMod 2)=0 := by
    obtain ⟨k,hk⟩ := he
    rw [hk,Int.cast_add]
    have hh : ∀ x : ZMod 2,x+x=0 := by decide
    exact hh _
  rw [hv,ZMod.val_zero,pow_zero]

/-- The character of -1 from the correction cancels the minus sign in the
odd-depth pole entry, leaving exactly the manuscript's sigma character. -/
theorem pole_character_correction (q : OddPrime) (e : ZMod q.val) (he : e^2=2) :
    quadraticChar (ZMod q.val) (-(2+e))*legendreSym q.val (-2)=bitSign (sigma q.val) := by
  have ht0 : (2 : ZMod q.val) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 q.val).mp hh
    exact q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left q.property.1.ne_one)
  have htwo : quadraticChar (ZMod q.val) (2 : ZMod q.val)=1 := by
    rw [← he]
    exact quadraticChar_sq_one' (by intro hz; apply ht0; rw [hz] at he; simpa using he.symm)
  have hneg : legendreSym q.val (-2)=quadraticChar (ZMod q.val) (-1) := by
    change quadraticChar (ZMod q.val) ((-2 : ℤ) : ZMod q.val)= _
    have heq : ((-2 : ℤ) : ZMod q.val)=(-1)*(2 : ZMod q.val) := by norm_num
    rw [heq,map_mul,htwo,mul_one]
  have hs := quadraticChar_sq_one (F:=ZMod q.val) (a:=(-1 : ZMod q.val)) (neg_ne_zero.mpr one_ne_zero)
  have hsig := sigma_character q.val q.property.2 e he
  change _= (-1 : ℤ)^(sigma q.val).val
  rw [← hsig,hneg,neg_eq_neg_one_mul,map_mul]
  calc
    _=(quadraticChar (ZMod q.val) (-1))^2*quadraticChar (ZMod q.val) (2+e) := by ring
    _=quadraticChar (ZMod q.val) (2+e) := by rw [hs,one_mul]

#print axioms constantSign_odd
#print axioms constantSign_odd_even
#print axioms pole_character_correction

end FourCorner.HasseConstantOdd
