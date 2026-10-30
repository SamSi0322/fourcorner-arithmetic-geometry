import HasseInertNormMin
import HasseTangentGlobal

namespace FourCorner.HasseInertSupport

open HilbertArithmeticHigh11 HasseInertNormMin HasseRationalSource HasseAnchorChoice

/-- The literal omission equations force t/z integral and the exact w/z
support identity at every odd inert prime, including poles of every depth. -/
theorem omission_support (q : OddPrime) (p v w t : ℚ_[q.val])
    (h2 : ¬ IsSquare (2 : ℚ_[q.val]))
    (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hv : v ≠ 0) (hw : w ≠ 0) (ht : t ≠ 0)
    (hV : v^2=2*t^2-4*p)
    (hW : (p-1)*w^2=2*(p+1)*(t^2-2)) :
    0≤t.valuation ∧ 2*w.valuation=(p+1).valuation-(p-1).valuation := by
  have hfour : (4 : ℚ_[q.val]).valuation=0 := by
    have he : (4 : ℚ_[q.val])=2^2 := by norm_num
    rw [he,Padic.valuation_pow,commonRoot_val_two q.property.2]
    simp
  have hnV : v^2-2*t^2= -4*p := by linear_combination hV
  have hminV := norm_form_val_min q.property.2 h2 v t hv ht
  have hvp : (v^2-2*t^2).valuation=p.valuation := by
    rw [hnV,Padic.valuation_mul (by norm_num) hp,commonRoot_val_neg,hfour,zero_add]
  rw [hvp] at hminV
  have hnW : t^2-2 ≠ 0 := by
    simpa using HasseInertNorm.norm_form_ne_zero h2 (Or.inr one_ne_zero : t ≠ 0 ∨ (1 : ℚ_[q.val]) ≠ 0)
  have hminW : (t^2-2).valuation=2*min t.valuation 0 := by
    simpa using norm_form_val_min q.property.2 h2 t 1 ht one_ne_zero
  have heW := congrArg Padic.valuation hW
  rw [Padic.valuation_mul ha (pow_ne_zero _ hw),Padic.valuation_pow,
    Padic.valuation_mul (mul_ne_zero (by norm_num) hb) hnW,
    Padic.valuation_mul (by norm_num) hb,commonRoot_val_two q.property.2,
    zero_add,hminW] at heW
  norm_num only [Nat.cast_ofNat] at heW
  have htIntegral : 0≤t.valuation := by
    by_contra hn
    have htneg : t.valuation<0 := by omega
    have hpneg : p.valuation<0 := by omega
    have hav : (p-1).valuation=p.valuation := by
      have hh := commonRoot_val_sub_of_ne hp (one_ne_zero : (1 : ℚ_[q.val]) ≠ 0)
        (show p.valuation ≠ (1 : ℚ_[q.val]).valuation by simpa using ne_of_lt hpneg)
      simpa only [Padic.valuation_one,min_eq_left (le_of_lt hpneg)] using hh
    have hbv : (p+1).valuation=p.valuation := by
      have hh := commonRoot_val_add_of_ne hp (one_ne_zero : (1 : ℚ_[q.val]) ≠ 0)
        (show p.valuation ≠ (1 : ℚ_[q.val]).valuation by simpa using ne_of_lt hpneg)
      simpa only [Padic.valuation_one,min_eq_left (le_of_lt hpneg)] using hh
    have hwv : w.valuation=t.valuation := by
      rw [hav,hbv,min_eq_left (le_of_lt htneg)] at heW
      omega
    let X : ℚ_[q.val] := 4*(p+1)/((p-1)*t^2)
    let Y : ℚ_[q.val] := 4/(p-1)
    have hX : X ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hb) (mul_ne_zero ha (pow_ne_zero _ ht))
    have hY : Y ≠ 0 := div_ne_zero (by norm_num) ha
    have hvX : 0<X.valuation := by
      dsimp [X]
      rw [commonRoot_val_div (mul_ne_zero (by norm_num) hb) (mul_ne_zero ha (pow_ne_zero _ ht)),
        Padic.valuation_mul (by norm_num) hb,hfour,Padic.valuation_mul ha (pow_ne_zero _ ht),
        Padic.valuation_pow,hav,hbv]
      norm_num only [Nat.cast_ofNat]
      omega
    have hvY : 0<Y.valuation := by
      dsimp [Y]
      rw [commonRoot_val_div (by norm_num) ha,hfour,hav]
      omega
    have hid : 2-(w/t)^2=X-Y := by
      dsimp [X,Y]
      field_simp
      linear_combination -hW
    have hratio : w/t ≠ 0 := div_ne_zero hw ht
    have hratioVal : (w/t).valuation=0 := by rw [commonRoot_val_div hw ht,hwv]; omega
    have hnorm : ‖(w/t)^2‖=1 := by
      rw [Padic.norm_eq_zpow_neg_valuation (pow_ne_zero _ hratio),Padic.valuation_pow,hratioVal]
      simp
    by_cases hdelta : 2-(w/t)^2=0
    · apply h2
      rw [sub_eq_zero.mp hdelta]
      exact IsSquare.sq _
    · apply h2
      apply padic_odd_isSquare_of_norm_sub_lt q.property.2 (pow_ne_zero 2 hratio) (IsSquare.sq (w/t))
      rw [hnorm]
      apply (commonRoot_norm_lt_one_iff hdelta).mpr
      have hdelta' : X + -Y ≠ 0 := by
        intro hh
        apply hdelta
        rw [hid]
        simpa only [sub_eq_add_neg] using hh
      have hh := Padic.le_valuation_add (x:=X) (y:=-Y) hdelta'
      rw [commonRoot_val_neg,← sub_eq_add_neg,← hid] at hh
      omega
  refine ⟨htIntegral,?_⟩
  rw [min_eq_right htIntegral] at heW
  omega

/-- Exact rational source support with the literal chosen anchor w/z. -/
theorem source_support (q : OddPrime) (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P)
    (h2 : ¬ IsSquare (2 : ℚ_[q.val])) :
    0≤padicValRat q.val (P.T/P.Z) ∧
      2*padicValRat q.val (D.w/P.Z)=padicValRat q.val (p+1)-padicValRat q.val (p-1) := by
  obtain ⟨hz,hu,hv,hw,ht⟩ := coordinates_ne_zero p hp P
  have hDw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hw
  have hpq : (p : ℚ_[q.val]) ≠ 0 := by exact_mod_cast (show p ≠ 0 by linarith)
  have haq : (p : ℚ_[q.val])-1 ≠ 0 := by exact_mod_cast (show p-1 ≠ 0 by linarith)
  have hbq : (p : ℚ_[q.val])+1 ≠ 0 := by exact_mod_cast (show p+1 ≠ 0 by linarith)
  have hvr : (P.V/P.Z)^2=2*(P.T/P.Z)^2-4*p := by
    field_simp
    linear_combination D.omission.1
  have hwr : (p-1)*(D.w/P.Z)^2=2*(p+1)*((P.T/P.Z)^2-2) := by
    field_simp
    linear_combination D.omission.2
  have hh := omission_support q (p : ℚ_[q.val]) (P.V/P.Z : ℚ) (D.w/P.Z : ℚ) (P.T/P.Z : ℚ)
    h2 hpq haq hbq (by exact_mod_cast div_ne_zero hv hz)
    (by exact_mod_cast div_ne_zero hDw hz) (by exact_mod_cast div_ne_zero ht hz)
    (by exact_mod_cast hvr) (by exact_mod_cast hwr)
  have hac : (p : ℚ_[q.val])-1=((p-1 : ℚ) : ℚ_[q.val]) := by simp
  have hbc : (p : ℚ_[q.val])+1=((p+1 : ℚ) : ℚ_[q.val]) := by simp
  simpa only [hac,hbc,Padic.valuation_ratCast] using hh

#print axioms omission_support
#print axioms source_support

end FourCorner.HasseInertSupport
