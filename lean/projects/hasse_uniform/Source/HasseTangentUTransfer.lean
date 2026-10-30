import HasseOddSymbolAlgebra
import HasseAntiDiagonal

namespace FourCorner.HasseTangentUTransfer
open HilbertArithmeticHigh11 HasseRationalSource HasseAnchorChoice HasseTangentGlobal
open HasseOddSymbol HasseOddSymbolAlgebra HasseAntiDiagonal

/-- The actual source involution U ↦ -U. -/
def flipU (p : ℚ) (P : HomogeneousPoint p) : HomogeneousPoint p where
  Z := P.Z
  U := -P.U
  V := P.V
  W := P.W
  T := P.T
  nonzero := by
    rintro ⟨hz,hu,hv,hw,ht⟩
    exact P.nonzero ⟨hz,neg_eq_zero.mp hu,hv,hw,ht⟩
  equations := by simpa only [CompleteSource11.Source,neg_sq] using P.equations

/-- The same actual anchor and W-sign survive this involution; its strict
real nonvanishing follows again from the actual positive conic. -/
def flipTangentData (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P) :
    TangentData p (flipU p P) where
  w := D.w
  sign := D.sign
  omission := D.omission
  separated := D.separated
  coefficient_negative := by
    have hz := (coordinates_ne_zero p hp P).1
    have htime := opposite_anchor_time p P.Z P.V D.w P.T hp hz D.omission
    have hanc := CompleteSource11.anchor_conic p P.Z P.V D.w P.T D.omission
    change (p-1)*(anchorU p P.Z D.w P.T)^2-p*(anchorT p P.Z D.w P.T)^2+
      p*(p+1)*(anchorZ p P.Z D.w)^2=0 at hanc
    have hpos := conic_polar_positive p P.Z (-P.U) P.T (anchorZ p P.Z D.w)
      (anchorU p P.Z D.w P.T) (anchorT p P.Z D.w P.T) hp
      (by rw [neg_sq]; linear_combination -P.equations.2.2) hanc D.separated htime
    change -p*secondPolar p P.Z (-P.U) P.T P.Z D.w P.T<0
    exact mul_neg_of_neg_of_pos (by linarith) hpos

/-- Genuine arithmetic transfer identity on the same original source. -/
theorem coefficient_flip_product (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p)
    (D : TangentData p P) :
    secondCoefficient p P D * secondCoefficient p (flipU p P) (flipTangentData p hp P D)=
      (p+1)*(p^2*(P.T*anchorZ p P.Z D.w-P.Z*anchorT p P.Z D.w P.T))^2 := by
  have hanc := CompleteSource11.anchor_conic p P.Z P.V D.w P.T D.omission
  change (p-1)*(anchorU p P.Z D.w P.T)^2-p*(anchorT p P.Z D.w P.T)^2+
    p*(p+1)*(anchorZ p P.Z D.w)^2=0 at hanc
  change (-p*secondPolar p P.Z P.U P.T P.Z D.w P.T)*
    (-p*secondPolar p P.Z (-P.U) P.T P.Z D.w P.T)=_
  dsimp [secondPolar]
  linear_combination -p^2*(p-1)*(anchorU p P.Z D.w P.T)^2*(-P.equations.2.2) -
    p^2*(p*P.T^2-p*(p+1)*P.Z^2)*hanc

private theorem eq_of_mul_eq_one (a b : ℤ) (h : a*b=1) : a=b := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨h1,h2⟩|⟨h1,h2⟩ <;> rw [h1,h2]

/-- Actual transfer across U sign when b is a completed square. This is an
explicit arithmetic comparison, with no local constancy premise. -/
theorem tangentSign_flipU_of_b_square (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hb : IsSquare ((p+1 : ℚ) : ℚ_[Q.val])) :
    tangentSign p hp P D Q.val=
      tangentSign p hp (flipU p P) (flipTangentData p hp P D) Q.val := by
  let E := flipTangentData p hp P D
  have ha0 : firstCoefficient p ≠ 0 := ne_of_lt (firstCoefficient_negative p hp)
  have hd0 : secondCoefficient p P D ≠ 0 := ne_of_lt D.coefficient_negative
  have he0 : secondCoefficient p (flipU p P) E ≠ 0 := ne_of_lt E.coefficient_negative
  have ha : (firstCoefficient p : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast ha0
  have hd : (secondCoefficient p P D : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hd0
  have he : (secondCoefficient p (flipU p P) E : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast he0
  have hsq : IsSquare ((secondCoefficient p P D : ℚ_[Q.val])*(secondCoefficient p (flipU p P) E : ℚ_[Q.val])) := by
    have hid := coefficient_flip_product p hp P D
    have hidq : (secondCoefficient p P D : ℚ_[Q.val])*(secondCoefficient p (flipU p P) E : ℚ_[Q.val])=
      ((p+1 : ℚ) : ℚ_[Q.val])*(((p^2*(P.T*anchorZ p P.Z D.w-P.Z*anchorT p P.Z D.w P.T) : ℚ) : ℚ_[Q.val]))^2 := by exact_mod_cast hid
    rw [hidq]
    exact hb.mul (IsSquare.sq _)
  have hm := oddSign_mul_right Q (firstCoefficient p : ℚ_[Q.val]) _ _ ha hd he
  rw [oddSign_one_of_right_square Q _ _ ha (mul_ne_zero hd he) hsq] at hm
  rw [tangentSign,rationalSign_eq_oddSign,tangentSign,rationalSign_eq_oddSign]
  exact eq_of_mul_eq_one _ _ hm.symm

/-- Actual U-sign transfer at every pole: b/a has square class one there,
and the exact coefficient product reduces to the proved anti-diagonal law. -/
theorem tangentSign_flipU_of_b_div_a_square (Q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (hb : IsSquare (((p+1)/(p-1) : ℚ) : ℚ_[Q.val])) :
    tangentSign p hp P D Q.val=
      tangentSign p hp (flipU p P) (flipTangentData p hp P D) Q.val := by
  let E := flipTangentData p hp P D
  have ha0 : firstCoefficient p ≠ 0 := ne_of_lt (firstCoefficient_negative p hp)
  have hd0 : secondCoefficient p P D ≠ 0 := ne_of_lt D.coefficient_negative
  have he0 : secondCoefficient p (flipU p P) E ≠ 0 := ne_of_lt E.coefficient_negative
  have ha : (firstCoefficient p : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast ha0
  have hd : (secondCoefficient p P D : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hd0
  have he : (secondCoefficient p (flipU p P) E : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast he0
  have hapos0 : p-1 ≠ 0 := by linarith
  have hapos : ((p-1 : ℚ) : ℚ_[Q.val]) ≠ 0 := by exact_mod_cast hapos0
  have hsq : IsSquare (((secondCoefficient p P D : ℚ_[Q.val])*(secondCoefficient p (flipU p P) E : ℚ_[Q.val]))/((p-1 : ℚ) : ℚ_[Q.val])) := by
    have hid := coefficient_flip_product p hp P D
    have hidq : ((secondCoefficient p P D : ℚ_[Q.val])*(secondCoefficient p (flipU p P) E : ℚ_[Q.val]))/((p-1 : ℚ) : ℚ_[Q.val])=
      (((p+1)/(p-1) : ℚ) : ℚ_[Q.val])*(((p^2*(P.T*anchorZ p P.Z D.w-P.Z*anchorT p P.Z D.w P.T) : ℚ) : ℚ_[Q.val]))^2 := by
      push_cast
      rw [← Rat.cast_mul, hid]
      push_cast
      ring
    rw [hidq]
    exact hb.mul (IsSquare.sq _)
  have hm := oddSign_mul_right Q (firstCoefficient p : ℚ_[Q.val]) _ _ ha hd he
  have heq := oddSign_eq_of_square_ratio Q (firstCoefficient p : ℚ_[Q.val]) _ ((p-1 : ℚ) : ℚ_[Q.val])
    ha (mul_ne_zero hd he) hapos hsq
  have hanti : oddSign Q (firstCoefficient p : ℚ_[Q.val]) ((p-1 : ℚ) : ℚ_[Q.val]) ha hapos=1 := by
    have hh := rationalSign_antidiagonal (firstCoefficient p) ha0 Q.val
    rw [rationalSign_eq_oddSign] at hh
    simpa only [firstCoefficient,neg_neg,Rat.cast_sub,Rat.cast_one,Rat.cast_neg] using hh
  rw [heq,hanti] at hm
  rw [tangentSign,rationalSign_eq_oddSign,tangentSign,rationalSign_eq_oddSign]
  exact eq_of_mul_eq_one _ _ hm.symm

#print axioms flipU
#print axioms flipTangentData
#print axioms coefficient_flip_product
#print axioms tangentSign_flipU_of_b_square
#print axioms tangentSign_flipU_of_b_div_a_square
end FourCorner.HasseTangentUTransfer
