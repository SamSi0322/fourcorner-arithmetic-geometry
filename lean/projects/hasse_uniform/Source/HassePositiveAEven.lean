import HassePositiveBInert

namespace FourCorner.HassePositiveAEven
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseRationalNormalization HasseConicTangentParity HasseOddBadModels
open HassePositiveBInert HasseHilbertArithmetic

/-- Direct original-source tangent parity at every positive even depth of a. -/
theorem secondCoefficient_positive_a_even (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h : ℕ) (hh : 0<h) (hva : padicValRat Q.val (p-1)=2*h) :
    Even (padicValRat Q.val (secondCoefficient p P D)) := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  obtain ⟨hZ,hU,hV,hW,hT⟩ := coordinates_ne_zero p hp P
  have hw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hW
  let r : ℚ := (Q.val : ℚ)^h
  have hr : r ≠ 0 := pow_ne_zero h (by exact_mod_cast Q.property.1.ne_zero)
  have hrv : padicValRat Q.val r=h := by
    dsimp [r]
    rw [padicValRat.pow,padicValRat.self Q.property.1.one_lt]
    simp
  let A : ℚ := (p-1)/r^2
  have hA : A ≠ 0 := div_ne_zero ha0 (pow_ne_zero _ hr)
  have hAv : padicValRat Q.val A=0 := by
    dsimp [A]
    rw [padicValRat.div ha0 (pow_ne_zero _ hr),padicValRat.pow,hrv,hva]
    norm_num
  obtain ⟨s,hs,hvu,hvt,hvz,hprim⟩ := exists_primitive_rational_scale (q:=Q.val)
    (r*P.U) P.T P.Z (mul_ne_zero hr hU) hT hZ
  let pp : ℚ_[Q.val] := p
  let rr : ℚ_[Q.val] := r
  let AA : ℚ_[Q.val] := A
  let u : ℚ_[Q.val] := (s*(r*P.U) : ℚ)
  let t : ℚ_[Q.val] := (s*P.T : ℚ)
  let z : ℚ_[Q.val] := (s*P.Z : ℚ)
  let w : ℚ_[Q.val] := (s*(r*D.w) : ℚ)
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
  have hAq : AA ≠ 0 := by dsimp [AA]; exact_mod_cast hA
  have huq : u ≠ 0 := by dsimp [u]; exact_mod_cast mul_ne_zero hs (mul_ne_zero hr hU)
  have htq : t ≠ 0 := by dsimp [t]; exact_mod_cast mul_ne_zero hs hT
  have hzq : z ≠ 0 := by dsimp [z]; exact_mod_cast mul_ne_zero hs hZ
  have hwq : w ≠ 0 := by dsimp [w]; exact_mod_cast mul_ne_zero hs (mul_ne_zero hr hw)
  have hrval : rr.valuation=h := by dsimp [rr]; rwa [Padic.valuation_ratCast]
  have hAval : AA.valuation=0 := by dsimp [AA]; rwa [Padic.valuation_ratCast]
  have haq : pp-1=rr^2*AA := by
    dsimp [pp,rr,AA,A]
    push_cast
    field_simp
  have haval : (pp-1).valuation=2*h := by
    have he : pp-1=((p-1 : ℚ) : ℚ_[Q.val]) := by simp [pp]
    rw [he,Padic.valuation_ratCast,hva]
  have haa0 : pp-1 ≠ 0 := by dsimp [pp]; exact_mod_cast ha0
  have hpval : pp.valuation=0 := commonRoot_val_eq_zero_of_sub_one_pos (by omega)
  have huval : 0≤u.valuation := by dsimp [u]; rwa [Padic.valuation_ratCast]
  have htval : 0≤t.valuation := by dsimp [t]; rwa [Padic.valuation_ratCast]
  have hzval : 0≤z.valuation := by dsimp [z]; rwa [Padic.valuation_ratCast]
  let pi := integralOfVal pp (by omega : 0≤pp.valuation)
  let ri := integralOfVal rr (by omega : 0≤rr.valuation)
  let Ai := integralOfVal AA (by omega : 0≤AA.valuation)
  let ui := integralOfVal u huval
  let ti := integralOfVal t htval
  let zi := integralOfVal z hzval
  have hpI : PadicInt.toZMod pi=1 := by
    have haI : PadicInt.toZMod (pi-1)=0 := by
      have he : (pi-1 : ℤ_[Q.val])=integralOfVal (pp-1) (by omega : 0≤(pp-1).valuation) := rfl
      rw [he]
      exact integral_residue_zero_of_positive _ (by omega)
    rw [map_sub,map_one] at haI
    linear_combination haI
  have hrI : PadicInt.toZMod ri=0 := integral_residue_zero_of_positive _ (by omega)
  have hAI : PadicInt.toZMod Ai ≠ 0 := integralOfVal_residue_ne_zero AA hAq hAval
  have hDU : AA*w^2=2*(pp+1)*(t^2-2*z^2) := by
    have he : A*(s*(r*D.w))^2=2*(p+1)*((s*P.T)^2-2*(s*P.Z)^2) := by
      dsimp [A]
      field_simp
      linear_combination D.omission.2
    dsimp [AA,w,pp,t,z]
    exact_mod_cast he
  let yi : ℤ_[Q.val] := 2*(pi+1)*(ti^2-2*zi^2)
  have hwval : 0≤w.valuation := integral_of_unit_times_square Ai w yi hAI hwq hDU
  let wi := integralOfVal w hwval
  have haI : pi-1=ri^2*Ai := Subtype.ext haq
  have hCI : Ai*ui^2-pi*ti^2+pi*(pi+1)*zi^2=0 := by
    apply Subtype.ext
    change AA*u^2-pp*t^2+pp*(pp+1)*z^2=0
    have he : A*(s*(r*P.U))^2-p*(s*P.T)^2+p*(p+1)*(s*P.Z)^2=0 := by
      dsimp [A]
      field_simp
      linear_combination -s^2*P.equations.2.2
    dsimp [AA,u,pp,t,z]
    exact_mod_cast he
  have hDUI : Ai*wi^2=2*(pi+1)*(ti^2-2*zi^2) := Subtype.ext hDU
  have hprimI : PadicInt.toZMod ui ≠ 0 ∨ PadicInt.toZMod ti ≠ 0 ∨ PadicInt.toZMod zi ≠ 0 := by
    rcases hprim with hu | ht | hz
    · exact Or.inl (integralOfVal_residue_ne_zero u huq (by dsimp [u]; rwa [Padic.valuation_ratCast]))
    · exact Or.inr (Or.inl (integralOfVal_residue_ne_zero t htq (by dsimp [t]; rwa [Padic.valuation_ratCast])))
    · exact Or.inr (Or.inr (integralOfVal_residue_ne_zero z hzq (by dsimp [z]; rwa [Padic.valuation_ratCast])))
  let L := secondPolar p P.Z P.U P.T P.Z D.w P.T
  have hL : L ≠ 0 := by
    intro he
    have hn := D.coefficient_negative
    change -p*L<0 at hn
    rw [he,mul_zero] at hn
    exact lt_irrefl _ hn
  let li := Ai*ui*(pi*(pi+1)*(wi+2*ri*ti+2*ri*zi))-
    pi*ti*(-(pi+1)*(ri*Ai*wi+2*pi*ti+2*ri^2*Ai*zi))+
    pi*(pi+1)*zi*(ri*Ai*wi-2*(pi+1)*zi)
  have hscale : (li : ℚ_[Q.val])=((s^2*L : ℚ) : ℚ_[Q.val]) := by
    change AA*u*(pp*(pp+1)*(w+2*rr*t+2*rr*z))-
      pp*t*(-(pp+1)*(rr*AA*w+2*pp*t+2*rr^2*AA*z))+
      pp*(pp+1)*z*(rr*AA*w-2*(pp+1)*z)=_
    dsimp [AA,u,pp,rr,w,t,z,L,A,secondPolar,anchorU,anchorT,anchorZ]
    push_cast
    field_simp
    <;> ring
  have hli : li ≠ 0 := by
    intro he
    have hn : ((s^2*L : ℚ) : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast mul_ne_zero (pow_ne_zero _ hs) hL
    apply hn
    rw [← hscale,he]
    rfl
  have heven := positive_a_even_model_tangent_even Q pi ri Ai ui ti zi wi hpI hrI hAI haI hCI hDUI hprimI hli
  change Even (li : ℚ_[Q.val]).valuation at heven
  rw [hscale,Padic.valuation_ratCast,padicValRat.mul (pow_ne_zero _ hs) hL,padicValRat.pow] at heven
  have hvp : padicValRat Q.val p=0 := by rwa [Padic.valuation_ratCast] at hpval
  change Even (padicValRat Q.val (-p*L))
  rw [padicValRat.mul (neg_ne_zero.mpr hp0) hL,padicValRat.neg,hvp,zero_add]
  rw [Int.even_iff] at heven ⊢
  norm_num only [Nat.cast_ofNat] at heven
  omega

theorem tangentSign_positive_a_even (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h : ℕ) (hh : 0<h) (hva : padicValRat Q.val (p-1)=2*h) :
    tangentSign p hp P D Q.val=1 := by
  rw [tangentSign]
  apply rationalSign_one_of_even_valuations Q
  · change Even (padicValRat Q.val (-(p-1)))
    rw [padicValRat.neg,hva]
    exact ⟨h,by ring⟩
  · exact secondCoefficient_positive_a_even Q p hp P D h hh hva

theorem tangentSign_positive_a_of_even (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : 0<padicValRat Q.val (p-1)) (he : Even (padicValRat Q.val (p-1))) :
    tangentSign p hp P D Q.val=1 := by
  obtain ⟨k,hk⟩ := he
  have hkpos : 0<k := by omega
  have hkn : (k.toNat : ℤ)=k := Int.toNat_of_nonneg (by omega)
  exact tangentSign_positive_a_even Q p hp P D k.toNat (by omega) (by omega)

/-- The exact constant-symbol table identity at every positive-a prime of
even depth; this includes the complete inert positive-a branch. -/
theorem tangentSign_positive_a_even_constant (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hv : 0<padicValRat Q.val (p-1)) (he : Even (padicValRat Q.val (p-1))) :
    tangentSign p hp P D Q.val=
      HilbertWellDefinedHigh11.rationalSign (firstCoefficient p) (-2)
        (ne_of_lt (firstCoefficient_negative p hp)) (by norm_num) Q.val := by
  rw [tangentSign_positive_a_of_even Q p hp P D hv he]
  symm
  apply rationalSign_one_of_even_valuations Q
  · change Even (padicValRat Q.val (-(p-1)))
    rwa [padicValRat.neg]
  · have htwo : padicValRat Q.val (2 : ℚ)=0 := by
      have hh := commonRoot_val_two Q.property.2
      rw [← Rat.cast_ofNat 2,Padic.valuation_ratCast] at hh
      exact hh
    rw [padicValRat.neg,htwo]
    exact ⟨0,by simp⟩

theorem tangentSign_positive_a_inert (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (hL : HasseNorms.Loc p) (P : HomogeneousPoint p) (D : TangentData p P)
    (h2 : ¬ IsSquare (2 : ZMod Q.val)) (hv : 0<padicValRat Q.val (p-1)) :
    tangentSign p hp P D Q.val=
      HilbertWellDefinedHigh11.rationalSign (firstCoefficient p) (-2)
        (ne_of_lt (firstCoefficient_negative p hp)) (by norm_num) Q.val := by
  apply tangentSign_positive_a_even_constant Q p hp P D hv
  exact (HasseNorms.local_inert_parities p hp hL Q.val Q.property.2
    (SqrtTwoGlobalNorm.nonsquare_two_completion h2)).2.1

#print axioms tangentSign_positive_a_of_even
#print axioms tangentSign_positive_a_even_constant
#print axioms tangentSign_positive_a_inert

#print axioms secondCoefficient_positive_a_even
#print axioms tangentSign_positive_a_even
end FourCorner.HassePositiveAEven
