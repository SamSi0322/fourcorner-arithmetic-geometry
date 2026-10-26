import HasseRationalNormalization
import HasseTangentGlobal

/-! The complete good-unit odd-prime row, directly for the rational tangent
symbol attached to an arbitrary genuine homogeneous source point. -/
namespace FourCorner.HasseGoodUnitRow

open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseRationalNormalization HasseConicTangentParity HasseHilbertArithmetic

theorem tangentSign_good_unit (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hvp : padicValRat q.val p=0) (hva : padicValRat q.val (p-1)=0)
    (hvb : padicValRat q.val (p+1)=0) : tangentSign p hp P D q.val=1 := by
  have hp0 : p ≠ 0 := by linarith
  have ha0 : p-1 ≠ 0 := by linarith
  have hb0 : p+1 ≠ 0 := by linarith
  obtain ⟨hZ,hU,hV,hW,hT⟩ := coordinates_ne_zero p hp P
  have hw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hW
  obtain ⟨s,hs,hvz,hvt,hvw,hprim⟩ := exists_primitive_rational_scale (q:=q.val)
    P.Z P.T D.w hZ hT hw
  let pp : ℚ_[q.val] := p
  let a : ℚ_[q.val] := pp-1
  let b : ℚ_[q.val] := pp+1
  let z : ℚ_[q.val] := (s*P.Z : ℚ)
  let u : ℚ_[q.val] := (s*P.U : ℚ)
  let w : ℚ_[q.val] := (s*D.w : ℚ)
  let t : ℚ_[q.val] := (s*P.T : ℚ)
  have hpq : pp ≠ 0 := by dsimp [pp]; exact_mod_cast hp0
  have haq : a ≠ 0 := by dsimp [a,pp]; exact_mod_cast ha0
  have hbq : b ≠ 0 := by dsimp [b,pp]; exact_mod_cast hb0
  have hzq : z ≠ 0 := by dsimp [z]; exact_mod_cast mul_ne_zero hs hZ
  have huq : u ≠ 0 := by dsimp [u]; exact_mod_cast mul_ne_zero hs hU
  have hwq : w ≠ 0 := by dsimp [w]; exact_mod_cast mul_ne_zero hs hw
  have htq : t ≠ 0 := by dsimp [t]; exact_mod_cast mul_ne_zero hs hT
  have hpv : pp.valuation=0 := by dsimp [pp]; rwa [Padic.valuation_ratCast]
  have hav : a.valuation=0 := by
    have he : a=((p-1 : ℚ) : ℚ_[q.val]) := by simp [a,pp]
    rw [he,Padic.valuation_ratCast]; exact hva
  have hbv : b.valuation=0 := by
    have he : b=((p+1 : ℚ) : ℚ_[q.val]) := by simp [b,pp]
    rw [he,Padic.valuation_ratCast]; exact hvb
  have hzv : 0≤z.valuation := by dsimp [z]; rwa [Padic.valuation_ratCast]
  have htv : 0≤t.valuation := by dsimp [t]; rwa [Padic.valuation_ratCast]
  have hwv : 0≤w.valuation := by dsimp [w]; rwa [Padic.valuation_ratCast]
  have hCr : (p-1)*(s*P.U)^2=p*(s*P.T)^2-p*(p+1)*(s*P.Z)^2 := by
    linear_combination -s^2*P.equations.2.2
  have hC : a*u^2=pp*t^2-pp*b*z^2 := by
    dsimp [a,b,pp,u,t,z]
    exact_mod_cast hCr
  have huv := conic_coordinate_integral a pp b u t z haq hpq hbq huq htq hzq
    hav hpv hbv htv hzv hC
  let pi := integralOfVal pp (by omega : 0≤pp.valuation)
  let zi := integralOfVal z hzv
  let ui := integralOfVal u huv
  let wi := integralOfVal w hwv
  let ti := integralOfVal t htv
  have hpi : PadicInt.toZMod pi ≠ 0 := integralOfVal_residue_ne_zero pp hpq hpv
  have hai : PadicInt.toZMod (pi-1) ≠ 0 := by
    exact integralOfVal_residue_ne_zero a haq hav
  have hbi : PadicInt.toZMod (pi+1) ≠ 0 := by
    exact integralOfVal_residue_ne_zero b hbq hbv
  have hprimI : PadicInt.toZMod zi ≠ 0 ∨ PadicInt.toZMod ti ≠ 0 ∨ PadicInt.toZMod wi ≠ 0 := by
    rcases hprim with hz0 | ht0 | hw0
    · exact Or.inl (integralOfVal_residue_ne_zero z hzq (by dsimp [z]; rwa [Padic.valuation_ratCast]))
    · exact Or.inr (Or.inl (integralOfVal_residue_ne_zero t htq (by dsimp [t]; rwa [Padic.valuation_ratCast])))
    · exact Or.inr (Or.inr (integralOfVal_residue_ne_zero w hwq (by dsimp [w]; rwa [Padic.valuation_ratCast])))
  have hDUr : (p-1)*(s*D.w)^2=2*(p+1)*((s*P.T)^2-2*(s*P.Z)^2) := by
    linear_combination s^2*D.omission.2
  have hDUi : (pi-1)*wi^2=2*(pi+1)*(ti^2-2*zi^2) := by
    apply Subtype.ext
    change (pp-1)*w^2=2*(pp+1)*(t^2-2*z^2)
    dsimp [pp,w,t,z]
    exact_mod_cast hDUr
  have hCi : (pi-1)*ui^2-pi*ti^2+pi*(pi+1)*zi^2=0 := by
    apply Subtype.ext
    change (pp-1)*u^2-pp*t^2+pp*(pp+1)*z^2=0
    linear_combination hC
  let L := secondPolar p P.Z P.U P.T P.Z D.w P.T
  have hL : L ≠ 0 := by
    intro h
    have hn := D.coefficient_negative
    change -p*L<0 at hn
    rw [h,mul_zero] at hn
    exact lt_irrefl _ hn
  let li := (pi-1)*(pi*(pi+1)*(wi+2*ti+2*zi))*ui-
    pi*(-(pi+1)*((pi-1)*wi+2*pi*ti+2*(pi-1)*zi))*ti+
    pi*(pi+1)*((pi-1)*wi-2*(pi+1)*zi)*zi
  have hscale : (li : ℚ_[q.val])=((s^2*L : ℚ) : ℚ_[q.val]) := by
    change (pp-1)*(pp*(pp+1)*(w+2*t+2*z))*u-
      pp*(-(pp+1)*((pp-1)*w+2*pp*t+2*(pp-1)*z))*t+
      pp*(pp+1)*((pp-1)*w-2*(pp+1)*z)*z= _
    dsimp [pp,w,t,z,u,L,secondPolar,anchorU,anchorT,anchorZ]
    push_cast
    ring
  have hli : li ≠ 0 := by
    intro h
    have hn : ((s^2*L : ℚ) : ℚ_[q.val]) ≠ 0 := by exact_mod_cast mul_ne_zero (pow_ne_zero _ hs) hL
    apply hn
    rw [← hscale,h]
    rfl
  have heven := integral_source_tangent_even q pi zi ui wi ti hpi hai hbi hDUi hCi hprimI hli
  change Even (li : ℚ_[q.val]).valuation at heven
  rw [hscale,Padic.valuation_ratCast,padicValRat.mul (pow_ne_zero _ hs) hL,padicValRat.pow] at heven
  have heL : Even (padicValRat q.val L) := by
    rw [Int.even_iff] at heven ⊢
    norm_num only [Nat.cast_ofNat] at heven
    omega
  rw [tangentSign]
  apply rationalSign_one_of_even_valuations q
  · change Even (padicValRat q.val (-(p-1)))
    rw [padicValRat.neg,hva]
    exact ⟨0,by simp⟩
  · change Even (padicValRat q.val (-p*L))
    rw [padicValRat.mul (neg_ne_zero.mpr hp0) hL,padicValRat.neg,hvp,zero_add]
    exact heL

#print axioms tangentSign_good_unit

end FourCorner.HasseGoodUnitRow
