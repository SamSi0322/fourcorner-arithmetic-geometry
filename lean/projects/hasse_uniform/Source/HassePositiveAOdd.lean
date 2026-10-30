import HassePositiveAOddCoordinates
namespace FourCorner.HassePositiveAOdd
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HassePoleParameters HassePositiveBInert HasseRationalNormalization HasseOddPoleCoordinates
open HasseOddPoleResidues HasseOddSymbol HasseOddSymbolAlgebra HasseLocalUnits
open HasseTangentUTransfer HasseTangentScaling HasseObstructionArithmetic HassePositiveAOddCoordinates
open HasseAntiDiagonal

private theorem residue_factor_square {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (t w : F) (ht : t^2=2) (hw : w^2=8) :
    IsSquare ((t+2)*(w+4)) ∧ (t+2)*(w+4) ≠ 0 := by
  have ht0 : t ≠ 0 := by
    intro he
    apply h2
    simpa only [he,zero_pow (by decide : 2 ≠ 0)] using ht.symm
  have htp : t+2 ≠ 0 := by
    intro he
    have he' : t= -2 := by linear_combination he
    rw [he'] at ht
    apply h2
    linear_combination ht
  have hwor : w=2*t ∨ w= -(2*t) := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    linear_combination hw-4*ht
  rcases hwor with hw | hw
  · have he : (t+2)*(w+4)=(t*(t+2))^2 := by
      rw [hw]
      linear_combination -(t^2+4*t+4)*ht
    rw [he]
    exact ⟨IsSquare.sq _,pow_ne_zero 2 (mul_ne_zero ht0 htp)⟩
  · have he : (t+2)*(w+4)=(2 : F)^2 := by rw [hw]; linear_combination -2*ht
    rw [he]
    exact ⟨IsSquare.sq _,pow_ne_zero 2 h2⟩

private theorem normalized_positive_u (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hZ : P.Z=1)
    (hv : 0<padicValRat Q.val (p-1))
    (u t w : ℤ_[Q.val])
    (hu : (u : ℚ_[Q.val])=(P.U : ℚ_[Q.val]))
    (ht : (t : ℚ_[Q.val])=(P.T : ℚ_[Q.val]))
    (hw : (w : ℚ_[Q.val])=(D.w : ℚ_[Q.val]))
    (hu1 : PadicInt.toZMod u=1) (ht2 : (PadicInt.toZMod t)^2=2)
    (hw8 : (PadicInt.toZMod w)^2=8) :
    tangentSign p hp P D Q.val=
      HilbertWellDefinedHigh11.rationalSign (firstCoefficient p) (-2)
        (ne_of_lt (firstCoefficient_negative p hp)) (by norm_num) Q.val := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  have hpdelta : 0<((p : ℚ_[Q.val])-1).valuation := by
    have he : (p : ℚ_[Q.val])-1=((p-1 : ℚ) : ℚ_[Q.val]) := by simp
    rw [he,Padic.valuation_ratCast]
    exact hv
  have hpval : (p : ℚ_[Q.val]).valuation=0 := commonRoot_val_eq_zero_of_sub_one_pos hpdelta
  let pi := integralOfVal (p : ℚ_[Q.val]) (by omega : 0≤(p : ℚ_[Q.val]).valuation)
  have hpi : PadicInt.toZMod pi=1 := integral_residue_one_of_sub_one_positive _ hpval hpdelta
  let Hi : ℤ_[Q.val] := (u+t+1)*(w+2*u)+2*(t+(pi+1))
  let H := reducedCoefficient p P D
  have hHcoe : (Hi : ℚ_[Q.val])=(H : ℚ_[Q.val]) := by
    change ((u : ℚ_[Q.val])+(t : ℚ_[Q.val])+1)*((w : ℚ_[Q.val])+2*(u : ℚ_[Q.val]))+
      2*((t : ℚ_[Q.val])+((p : ℚ_[Q.val])+1))=_
    rw [hu,ht,hw]
    dsimp [H,reducedCoefficient]
    rw [hZ]
    push_cast
    ring
  have hHres : PadicInt.toZMod Hi=(PadicInt.toZMod t+2)*(PadicInt.toZMod w+4) := by
    dsimp [Hi]
    simp only [map_add,map_mul,map_ofNat,map_one,hu1,hpi]
    ring
  have htwo : (2 : ZMod Q.val) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 2 Q.val).mp he
    exact Q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left Q.property.1.ne_one)
  have hHrf := residue_factor_square htwo (PadicInt.toZMod t) (PadicInt.toZMod w) ht2 hw8
  have hHsq : IsSquare (H : ℚ_[Q.val]) := by
    rw [← hHcoe]
    apply (padicInt_isSquare_coe_iff_residue_unit Q.property.2 Hi (by rw [hHres]; exact hHrf.2)).mpr
    rw [hHres]
    exact hHrf.1
  have hHq : (H : ℚ_[Q.val]) ≠ 0 := by
    rw [← hHcoe]
    exact PadicInt.coe_ne_zero.mpr (fun he => hHrf.2 (by rw [← hHres,he,map_zero]))
  have hH0 : H ≠ 0 := by intro he; exact hHq (by simp [he])
  have hbhalf : IsSquare (((p+1)/2 : ℚ) : ℚ_[Q.val]) := by
    let y : ℚ_[Q.val] := (((p+1)/2 : ℚ) : ℚ_[Q.val])
    have he : y-1=(((p-1)/2 : ℚ) : ℚ_[Q.val]) := by
      dsimp [y]
      exact_mod_cast (show (p+1)/2-1=(p-1)/2 by ring)
    have hn : y-1 ≠ 0 := by rw [he]; exact_mod_cast div_ne_zero ha0 (by norm_num : (2 : ℚ) ≠ 0)
    apply square_of_positive_perturbation Q 1 y one_ne_zero Padic.valuation_one IsSquare.one hn
    rw [he,Padic.valuation_ratCast,padicValRat.div ha0 (by norm_num : (2 : ℚ) ≠ 0)]
    have h2val : padicValRat Q.val (2 : ℚ)=0 := by
      have hh := commonRoot_val_two Q.property.2
      rw [← Rat.cast_ofNat 2,Padic.valuation_ratCast] at hh
      exact hh
    rw [h2val,sub_zero]
    exact hv
  have hx0 : firstCoefficient p ≠ 0 := ne_of_lt (firstCoefficient_negative p hp)
  have hd0 : secondCoefficient p P D ≠ 0 := ne_of_lt D.coefficient_negative
  have hx : (firstCoefficient p : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hx0
  have hd : (secondCoefficient p P D : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hd0
  have ha : ((p-1 : ℚ) : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast ha0
  have hm2 : (-2 : ℚ_[Q.val]) ≠ 0 := by norm_num
  have hz : (((p-1 : ℚ) : ℚ_[Q.val])*(-2)) ≠ 0 := mul_ne_zero ha hm2
  have hsq : IsSquare ((secondCoefficient p P D : ℚ_[Q.val])/((((p-1 : ℚ) : ℚ_[Q.val])*(-2)))) := by
    have he : (secondCoefficient p P D : ℚ_[Q.val])/((((p-1 : ℚ) : ℚ_[Q.val])*(-2)))=
        (p : ℚ_[Q.val])^2*((((p+1)/2 : ℚ) : ℚ_[Q.val]))*(H : ℚ_[Q.val]) := by
      have hf := secondCoefficient_factor p P D
      have hr : secondCoefficient p P D/((p-1)*(-2))=p^2*((p+1)/2)*H := by rw [hf]; field_simp <;> ring
      exact_mod_cast hr
    rw [he]
    exact ((IsSquare.sq (p : ℚ_[Q.val])).mul hbhalf).mul hHsq
  have heq := oddSign_eq_of_square_ratio Q (firstCoefficient p : ℚ_[Q.val]) _ _ hx hd hz hsq
  have hanti : oddSign Q (firstCoefficient p : ℚ_[Q.val]) ((p-1 : ℚ) : ℚ_[Q.val]) hx ha=1 := by
    have hh := rationalSign_antidiagonal (firstCoefficient p) hx0 Q.val
    rw [rationalSign_eq_oddSign] at hh
    simpa only [firstCoefficient,neg_neg,Rat.cast_sub,Rat.cast_one,Rat.cast_neg] using hh
  rw [tangentSign,rationalSign_eq_oddSign,heq,oddSign_mul_right Q _ _ _ hx ha hm2,hanti,one_mul,
    rationalSign_eq_oddSign]
  norm_num only [Rat.cast_neg,Rat.cast_ofNat]

theorem tangentSign_positive_a_odd_normalized (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (hZ : P.Z=1)
    (hv : 0<padicValRat Q.val (p-1)) (hodd : Odd (padicValRat Q.val (p-1))) :
    tangentSign p hp P D Q.val=
      HilbertWellDefinedHigh11.rationalSign (firstCoefficient p) (-2)
        (ne_of_lt (firstCoefficient_negative p hp)) (by norm_num) Q.val := by
  obtain ⟨u,t,w,hu,ht,hw,hu2,ht2,hw8⟩ := residue_coordinates Q p hp P D hZ hv hodd
  have huor : PadicInt.toZMod u=1 ∨ PadicInt.toZMod u= -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hu2)
  rcases huor with hu1 | hum1
  · exact normalized_positive_u Q p hp P D hZ hv u t w hu ht hw hu1 ht2 hw8
  · have htwo : (2 : ZMod Q.val) ≠ 0 := by
      intro he
      have hd := (ZMod.natCast_eq_zero_iff 2 Q.val).mp he
      exact Q.property.2 ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left Q.property.1.ne_one)
    have hsq2r : IsSquare (2 : ZMod Q.val) := ⟨PadicInt.toZMod t,by simpa only [pow_two] using ht2.symm⟩
    have hsq2 : IsSquare (2 : ℚ_[Q.val]) := by
      exact (padicInt_isSquare_coe_iff_residue_unit Q.property.2 (2 : ℤ_[Q.val])
        (by simpa only [map_ofNat] using htwo)).mpr (by simpa only [map_ofNat] using hsq2r)
    have ha0 : p-1 ≠ 0 := by linarith
    have hb : IsSquare (((p+1 : ℚ) : ℚ_[Q.val])) := by
      have he : (((p+1 : ℚ) : ℚ_[Q.val]))-2=(((p-1 : ℚ) : ℚ_[Q.val])) := by push_cast; ring
      apply square_of_positive_perturbation Q 2 _ (by norm_num) (commonRoot_val_two Q.property.2) hsq2
      · rw [he]
        exact_mod_cast ha0
      · rw [he,Padic.valuation_ratCast]
        exact hv
    rw [tangentSign_flipU_of_b_square Q p hp P D hb]
    apply normalized_positive_u Q p hp (flipU p P) (flipTangentData p hp P D) hZ hv (-u) t w
    · simpa only [PadicInt.coe_neg,flipU,Rat.cast_neg] using congrArg Neg.neg hu
    · exact ht
    · exact hw
    · simp only [map_neg,hum1,neg_neg]
    · exact ht2
    · exact hw8

/-- Full positive-a odd-depth row for the original source. -/
theorem tangentSign_positive_a_odd (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : 0<padicValRat Q.val (p-1)) (hodd : Odd (padicValRat Q.val (p-1))) :
    tangentSign p hp P D Q.val=
      HilbertWellDefinedHigh11.rationalSign (firstCoefficient p) (-2)
        (ne_of_lt (firstCoefficient_negative p hp)) (by norm_num) Q.val := by
  have hZ0 := (coordinates_ne_zero p hp P).1
  let s := P.Z⁻¹
  have hs : s ≠ 0 := inv_ne_zero hZ0
  let R := scalePoint p P s hs
  let E := scaleTangentData p P D s hs
  have hRZ : R.Z=1 := by change P.Z⁻¹*P.Z=1; exact inv_mul_cancel₀ hZ0
  rw [← tangentSign_scale p hp P D s hs Q.val]
  exact tangentSign_positive_a_odd_normalized Q p hp R E hRZ hv hodd

/-- Entire positive-a row of the literal odd table: no depth restriction,
no chosen local evaluation point, and no extra solubility hypothesis. -/
theorem tangentSign_positive_a (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : 0<padicValRat Q.val (p-1)) :
    tangentSign p hp P D Q.val=
      HilbertWellDefinedHigh11.rationalSign (firstCoefficient p) (-2)
        (ne_of_lt (firstCoefficient_negative p hp)) (by norm_num) Q.val := by
  by_cases he : Even (padicValRat Q.val (p-1))
  · exact HassePositiveAEven.tangentSign_positive_a_even_constant Q p hp P D hv he
  · exact tangentSign_positive_a_odd Q p hp P D hv (Int.not_even_iff_odd.mp he)

#print axioms tangentSign_positive_a_odd_normalized
#print axioms tangentSign_positive_a_odd
#print axioms tangentSign_positive_a

#print axioms residue_factor_square
#print axioms normalized_positive_u
end FourCorner.HassePositiveAOdd
