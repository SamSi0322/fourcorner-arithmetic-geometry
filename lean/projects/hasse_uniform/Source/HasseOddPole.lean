import HasseOddPoleResidues
namespace FourCorner.HasseOddPole
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HassePoleParameters HassePositiveBInert HasseRationalNormalization HasseOddPoleCoordinates
open HasseOddPoleResidues HasseOddSymbol HasseOddSymbolAlgebra HasseLocalUnits
open HasseTangentUTransfer HasseTangentScaling HasseObstructionArithmetic

private theorem normalized_positive_u (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hT : P.T=1)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p))
    (u w z : ℤ_[Q.val])
    (hu : (u : ℚ_[Q.val])=(P.U : ℚ_[Q.val]))
    (hw : (w : ℚ_[Q.val])=(D.w : ℚ_[Q.val]))
    (hz : (z : ℚ_[Q.val])=(P.Z : ℚ_[Q.val]))
    (hu1 : PadicInt.toZMod u=1) (hw2 : (PadicInt.toZMod w)^2=2)
    (hz0 : PadicInt.toZMod z=0) :
    tangentSign p hp P D Q.val=
      quadraticChar (ZMod Q.val) (-1)*(-1 : ℤ)^(sigma Q.val).val := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  have hb0 : p+1 ≠ 0 := by linarith
  obtain ⟨hZ,hU,hV,hW,hTT⟩ := coordinates_ne_zero p hp P
  let bz2 : ℚ_[Q.val] := (((p+1)*P.Z^2 : ℚ) : ℚ_[Q.val])
  have hbzv : 0<bz2.valuation := by
    dsimp [bz2]
    rw [Padic.valuation_ratCast,padicValRat.mul hb0 (pow_ne_zero _ hZ),padicValRat.pow]
    have hb := pole_b_valuation Q p hp hv
    rw [Padic.valuation_ratCast,Padic.valuation_ratCast] at hb
    rw [hb]
    exact z_depth_at_odd_pole Q p hp P D hT hv hodd
  let bzi := integralOfVal bz2 (by omega : 0≤bz2.valuation)
  have hbzi : PadicInt.toZMod bzi=0 := integral_residue_zero_of_positive bz2 hbzv
  let Hi : ℤ_[Q.val] := (u+1+z)*(w+2*u)+2*z+2*bzi
  let H := reducedCoefficient p P D
  have hHcoe : (Hi : ℚ_[Q.val])=(H : ℚ_[Q.val]) := by
    change ((u : ℚ_[Q.val])+1+(z : ℚ_[Q.val]))*((w : ℚ_[Q.val])+2*(u : ℚ_[Q.val]))+
      2*(z : ℚ_[Q.val])+2*bz2=_
    rw [hu,hw,hz]
    dsimp [H,reducedCoefficient,bz2]
    rw [hT]
    push_cast
    ring
  have hHres : PadicInt.toZMod Hi=2*(2+PadicInt.toZMod w) := by
    dsimp [Hi]
    simp only [map_add,map_mul,map_ofNat,map_one,hu1,hz0,hbzi]
    ring
  have htwo : (2 : ZMod Q.val) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 2 Q.val).mp he
    exact Q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left Q.property.1.ne_one)
  have hwplus : 2+PadicInt.toZMod w ≠ 0 := by
    intro he
    have hew : PadicInt.toZMod w= -2 := by linear_combination he
    rw [hew] at hw2
    apply htwo
    linear_combination hw2
  have hHi : PadicInt.toZMod Hi ≠ 0 := by rw [hHres]; exact mul_ne_zero htwo hwplus
  have hHq : (H : ℚ_[Q.val]) ≠ 0 := by
    rw [← hHcoe]
    exact PadicInt.coe_ne_zero.mpr (fun he => hHi (by simp [he]))
  have hH0 : H ≠ 0 := by intro he; exact hHq (by simp [he])
  have hHval : (H : ℚ_[Q.val]).valuation=0 := by rw [← hHcoe]; exact HasseConicTangentParity.valuation_zero_of_residue_ne_zero Hi hHi
  have hbdiv := pole_b_div_a_square Q p hp hv
  have hab : IsSquare ((((p-1)*(p+1) : ℚ) : ℚ_[Q.val])) := by
    have hh := (IsSquare.sq (((p-1 : ℚ) : ℚ_[Q.val]))).mul hbdiv
    have he : (((p-1 : ℚ) : ℚ_[Q.val]))^2*(((p+1)/(p-1) : ℚ) : ℚ_[Q.val])=
        (((p-1)*(p+1) : ℚ) : ℚ_[Q.val]) := by
      exact_mod_cast (show (p-1)^2*((p+1)/(p-1))=(p-1)*(p+1) from by field_simp <;> ring)
    rwa [he] at hh
  have hx0 : firstCoefficient p ≠ 0 := ne_of_lt (firstCoefficient_negative p hp)
  have hd0 : secondCoefficient p P D ≠ 0 := ne_of_lt D.coefficient_negative
  have hx : (firstCoefficient p : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hx0
  have hd : (secondCoefficient p P D : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hd0
  have hmH : (-(H : ℚ_[Q.val])) ≠ 0 := neg_ne_zero.mpr hHq
  have hsq : IsSquare ((secondCoefficient p P D : ℚ_[Q.val])/(-(H : ℚ_[Q.val]))) := by
    have he : (secondCoefficient p P D : ℚ_[Q.val])/(-(H : ℚ_[Q.val]))=
        (p : ℚ_[Q.val])^2*(((p-1)*(p+1) : ℚ) : ℚ_[Q.val]) := by
      have hf := secondCoefficient_factor p P D
      have her : secondCoefficient p P D/(-H)=p^2*((p-1)*(p+1)) := by rw [hf]; change -p^2*(p-1)*(p+1)*H/(-H)=_; field_simp [hH0] <;> ring
      exact_mod_cast her
    rw [he]
    exact (IsSquare.sq (p : ℚ_[Q.val])).mul hab
  have heq := oddSign_eq_of_square_ratio Q (firstCoefficient p : ℚ_[Q.val]) _ (-(H : ℚ_[Q.val])) hx hd hmH hsq
  have hxval : (((firstCoefficient p : ℚ_[Q.val]).valuation : ℤ) : ZMod 2)=1 := by
    have hodd' : Odd (firstCoefficient p : ℚ_[Q.val]).valuation := by
      change Odd (-( ((p-1 : ℚ) : ℚ_[Q.val]))).valuation
      rw [commonRoot_val_neg,pole_a_valuation Q p hp hv,Padic.valuation_ratCast]
      exact hodd
    rw [Int.odd_iff] at hodd'
    rw [← ZMod.intCast_mod]
    norm_num only [Nat.cast_ofNat]
    rw [hodd']
    norm_num
  have hyval : (-(H : ℚ_[Q.val])).valuation=0 := by rw [commonRoot_val_neg,hHval]
  have hrH : residue (-(H : ℚ_[Q.val])) hmH= -(PadicInt.toZMod Hi) := by
    rw [residue_eq_integral_residue _ hmH hyval]
    have he : integralOfVal (-(H : ℚ_[Q.val])) (by omega : 0≤(-(H : ℚ_[Q.val])).valuation)= -Hi := by
      apply Subtype.ext
      simpa only [coe_integralOfVal,PadicInt.coe_neg] using congrArg Neg.neg hHcoe.symm
    rw [he,map_neg]
  have hchar : quadraticChar (ZMod Q.val) (-(PadicInt.toZMod Hi))=
      quadraticChar (ZMod Q.val) (-1)*(-1 : ℤ)^(sigma Q.val).val := by
    rw [hHres]
    have he : -(2*(2+PadicInt.toZMod w))=(-1)*2*(2+PadicInt.toZMod w) := by ring
    rw [he,map_mul,map_mul]
    have hs2 : IsSquare (2 : ZMod Q.val) := ⟨PadicInt.toZMod w,by simpa only [pow_two] using hw2.symm⟩
    rw [(quadraticChar_one_iff_isSquare htwo).mpr hs2, mul_one,
      sigma_character Q.val Q.property.2 (PadicInt.toZMod w) hw2]
  rw [tangentSign,rationalSign_eq_oddSign,heq]
  simp only [oddSign,hxval,hyval,Int.cast_zero,ZMod.val_zero,mul_zero,pow_zero,one_mul,ZMod.val_one_eq_one_mod]
  norm_num only [Nat.mod_succ_eq_iff_lt.mpr (by decide : 1<2),pow_one]
  rw [hrH]
  simpa only [zero_mul,pow_zero,one_mul] using hchar

theorem tangentSign_odd_pole_normalized (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hT : P.T=1)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p)) :
    tangentSign p hp P D Q.val=
      quadraticChar (ZMod Q.val) (-1)*(-1 : ℤ)^(sigma Q.val).val := by
  obtain ⟨u,w,z,hu,hw,hz,hu2,hw2,hz0⟩ := residue_coordinates_at_odd_pole Q p hp P D hT hv hodd
  have huor : PadicInt.toZMod u=1 ∨ PadicInt.toZMod u= -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hu2)
  rcases huor with hu1 | hum1
  · exact normalized_positive_u Q p hp P D hT hv hodd u w z hu hw hz hu1 hw2 hz0
  · rw [tangentSign_flipU_of_b_div_a_square Q p hp P D (pole_b_div_a_square Q p hp hv)]
    apply normalized_positive_u Q p hp (flipU p P) (flipTangentData p hp P D) hT hv hodd (-u) w z
    · simpa only [PadicInt.coe_neg,flipU,Rat.cast_neg] using congrArg Neg.neg hu
    · exact hw
    · exact hz
    · simp only [map_neg,hum1,neg_neg]
    · exact hw2
    · exact hz0

/-- Complete direct odd-pole evaluation for the original source and actual
chosen tangent data. Rational scaling and the proved U-sign transfer account
for all charts; no local-point constancy assumption is made. -/
theorem tangentSign_odd_pole_bit (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p)) :
    tangentSign p hp P D Q.val=
      quadraticChar (ZMod Q.val) (-1)*(-1 : ℤ)^(sigma Q.val).val := by
  have hT0 := (coordinates_ne_zero p hp P).2.2.2.2
  let s := P.T⁻¹
  have hs : s ≠ 0 := inv_ne_zero hT0
  let R := scalePoint p P s hs
  let E := scaleTangentData p P D s hs
  have hRT : R.T=1 := by change P.T⁻¹*P.T=1; exact inv_mul_cancel₀ hT0
  rw [← tangentSign_scale p hp P D s hs Q.val]
  exact tangentSign_odd_pole_normalized Q p hp R E hRT hv hodd

/-- Exact character of -(2+e), for either literal root of 2. -/
theorem tangentSign_odd_pole_character (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p))
    (e : ZMod Q.val) (he : e^2=2) :
    tangentSign p hp P D Q.val=quadraticChar (ZMod Q.val) (-(2+e)) := by
  rw [tangentSign_odd_pole_bit Q p hp P D hv hodd,← sigma_character Q.val Q.property.2 e he,← map_mul]
  congr 1
  ring

theorem tangentSign_odd_pole (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (hL : HasseNorms.Loc p) (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : padicValRat Q.val p<0) (hodd : Odd (padicValRat Q.val p)) :
    tangentSign p hp P D Q.val=quadraticChar (ZMod Q.val) (-(2+rootTwo Q.val)) := by
  exact tangentSign_odd_pole_character Q p hp P D hv hodd (rootTwo Q.val)
    (rootTwo_sq Q.val (pole_root_exists p hp hL Q.val Q.property.2 hodd))

#print axioms tangentSign_odd_pole_normalized
#print axioms tangentSign_odd_pole_bit
#print axioms tangentSign_odd_pole_character
#print axioms tangentSign_odd_pole
#print axioms normalized_positive_u
end FourCorner.HasseOddPole
