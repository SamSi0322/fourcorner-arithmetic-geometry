import LocalKummerSelection
import CSFoundation.CommonSourceDyadicOrders

noncomputable section
namespace FourCorner.CommonSource

lemma Tplus_add_T0_eq_Tminus (n : ℚ) (hn : n ≠ 0) :
    Tplus n hn + T0 n hn = Tminus n hn := by
  apply coordinates_injective
  have hc := coordinates_add_T0 hn (x:=n) (y:=0)
    (by simp [CongruentEquation]) hn
  change coordinates (finitePoint hn _ + T0 n hn) = some (-n,0)
  rw [hc]
  congr 1
  apply Prod.ext
  · dsimp
    field_simp
  · simp

lemma Tplus_add_Tminus_eq_T0 (n : ℚ) (hn : n ≠ 0) :
    Tplus n hn+Tminus n hn=T0 n hn := by
  rw [← Tplus_add_T0_eq_Tminus n hn,← add_assoc,Tplus_add_self,zero_add]

/-- Exhaustive actual torsion-pair labels when the sum is T0. -/
theorem torsion_pairs_one (n : ℚ) (hn : n ≠ 0) (P Q : Point n)
    (hP : 2 • P=0) (hs : P+Q=T0 n hn) :
    (P=T0 n hn ∧ Q=0) ∨ (P=0 ∧ Q=T0 n hn) ∨
    (P=Tminus n hn ∧ Q=Tplus n hn) ∨ (P=Tplus n hn ∧ Q=Tminus n hn) := by
  rcases (two_torsion_iff hn P).mp hP with h | h | h | h
  · exact Or.inr (Or.inl ⟨h,by simpa [h,O] using hs⟩)
  · refine Or.inl ⟨h,?_⟩
    apply add_left_cancel (a:=T0 n hn)
    simpa [h] using hs
  · refine Or.inr (Or.inr (Or.inr ⟨h,?_⟩))
    apply add_left_cancel (a:=Tplus n hn)
    rw [← Tplus_add_Tminus_eq_T0 n hn] at hs
    simpa [h] using hs
  · refine Or.inr (Or.inr (Or.inl ⟨h,?_⟩))
    apply add_left_cancel (a:=Tminus n hn)
    rw [← Tplus_add_Tminus_eq_T0 n hn,add_comm (Tplus n hn)] at hs
    simpa [h] using hs

/-- Exhaustive actual torsion-pair labels when the sum is zero. -/
theorem torsion_pairs_seven (n : ℚ) (hn : n ≠ 0) (P Q : Point n)
    (hP : 2 • P=0) (hs : P+Q=0) :
    (P=Tplus n hn ∧ Q=Tplus n hn) ∨ (P=Tminus n hn ∧ Q=Tminus n hn) ∨
    (P=0 ∧ Q=0) ∨ (P=T0 n hn ∧ Q=T0 n hn) := by
  have hQP : Q=P := by
    apply add_left_cancel (a:=P)
    rw [hs,← two_nsmul,hP]
  rcases (two_torsion_iff hn P).mp hP with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl ⟨h,hQP.trans h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h,hQP.trans h⟩))
  · exact Or.inl ⟨h,hQP.trans h⟩
  · exact Or.inr (Or.inl ⟨h,hQP.trans h⟩)

lemma abscissa_add_zero {n a b x y : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hU : CongruentEquation n x y)
    (h : finitePoint hn hQ=finitePoint hn hU+0) : a=x := by
  have hc := congrArg coordinates h
  simpa using congrArg (fun z : Option (ℚ×ℚ) => z.map Prod.fst) hc

lemma abscissa_add_T0 {n a b x y : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hU : CongruentEquation n x y) (hx : x ≠ 0)
    (h : finitePoint hn hQ=finitePoint hn hU+T0 n hn) :
    a=commonSourceTranslateZero n x := by
  have hc := congrArg coordinates h
  rw [coordinates_finitePoint,coordinates_add_T0 hn hU hx] at hc
  exact congrArg Prod.fst (Option.some.inj hc)

lemma abscissa_add_Tplus {n a b x y : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hU : CongruentEquation n x y) (hx : x-n ≠ 0)
    (h : finitePoint hn hQ=finitePoint hn hU+Tplus n hn) :
    a=commonSourceTranslatePlus n x := by
  have hc := congrArg coordinates h
  rw [coordinates_finitePoint,coordinates_add_Tplus hn hU (sub_ne_zero.mp hx)] at hc
  exact congrArg Prod.fst (Option.some.inj hc)

lemma abscissa_add_Tminus {n a b x y : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hU : CongruentEquation n x y) (hx : x+n ≠ 0)
    (h : finitePoint hn hQ=finitePoint hn hU+Tminus n hn) :
    a=commonSourceTranslateMinus n x := by
  have hc := congrArg coordinates h
  rw [coordinates_finitePoint,coordinates_add_Tminus hn hU (by intro h; simp [h] at hx)] at hc
  exact congrArg Prod.fst (Option.some.inj hc)

/-- The true group-theoretic label relation supplies precisely the four dyadic
coordinate orders; no independent choice of the two local labels is made. -/
theorem actual_coordinate_orders_one {n a b c e x y w z : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c e)
    (hU : CongruentEquation n x y) (hV : CongruentEquation n w z)
    (hx : x ≠ 0) (hxm : x-n ≠ 0) (hxp : x+n ≠ 0)
    (hw : w ≠ 0) (hwm : w-n ≠ 0) (hwp : w+n ≠ 0)
    (τQ τR : Point n) (htQ : 2 • τQ=0) (hs : τQ+τR=T0 n hn)
    (hQU : finitePoint hn hQ=finitePoint hn hU+τQ)
    (hRV : finitePoint hn hR=finitePoint hn hV+τR) :
    commonSourceDyadicOrdersOne (n:ℚ_[2]) x w a c := by
  rcases torsion_pairs_one n hn τQ τR htQ hs with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · left
    constructor
    · have h := abscissa_add_T0 hn hQ hU hx hQU
      simpa only [commonSourceTranslateZero,Rat.cast_div,Rat.cast_neg,Rat.cast_pow] using
        congrArg (fun t : ℚ => (t:ℚ_[2])) h
    · exact_mod_cast abscissa_add_zero hn hR hV hRV
  · right;left
    constructor
    · exact_mod_cast abscissa_add_zero hn hQ hU hQU
    · have h := abscissa_add_T0 hn hR hV hw hRV
      simpa only [commonSourceTranslateZero,Rat.cast_div,Rat.cast_neg,Rat.cast_pow] using
        congrArg (fun t : ℚ => (t:ℚ_[2])) h
  · right;right;left
    constructor
    · have h := abscissa_add_Tminus hn hQ hU hxp hQU
      simpa [commonSourceTranslateMinus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h
    · have h := abscissa_add_Tplus hn hR hV hwm hRV
      simpa [commonSourceTranslatePlus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h
  · right;right;right
    constructor
    · have h := abscissa_add_Tplus hn hQ hU hxm hQU
      simpa [commonSourceTranslatePlus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h
    · have h := abscissa_add_Tminus hn hR hV hwp hRV
      simpa [commonSourceTranslateMinus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h

theorem actual_coordinate_orders_seven {n a b c e x y w z : ℚ} (hn : n ≠ 0)
    (hQ : CongruentEquation n a b) (hR : CongruentEquation n c e)
    (hU : CongruentEquation n x y) (hV : CongruentEquation n w z)
    (hx : x ≠ 0) (hxm : x-n ≠ 0) (hxp : x+n ≠ 0)
    (hw : w ≠ 0) (hwm : w-n ≠ 0) (hwp : w+n ≠ 0)
    (τQ τR : Point n) (htQ : 2 • τQ=0) (hs : τQ+τR=0)
    (hQU : finitePoint hn hQ=finitePoint hn hU+τQ)
    (hRV : finitePoint hn hR=finitePoint hn hV+τR) :
    commonSourceDyadicOrdersSeven (n:ℚ_[2]) x w a c := by
  rcases torsion_pairs_seven n hn τQ τR htQ hs with
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · left
    constructor
    · have h := abscissa_add_Tplus hn hQ hU hxm hQU
      simpa [commonSourceTranslatePlus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h
    · have h := abscissa_add_Tplus hn hR hV hwm hRV
      simpa [commonSourceTranslatePlus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h
  · right;left
    constructor
    · have h := abscissa_add_Tminus hn hQ hU hxp hQU
      simpa [commonSourceTranslateMinus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h
    · have h := abscissa_add_Tminus hn hR hV hwp hRV
      simpa [commonSourceTranslateMinus] using congrArg (fun t : ℚ => (t:ℚ_[2])) h
  · right;right;left
    constructor
    · exact_mod_cast abscissa_add_zero hn hQ hU hQU
    · exact_mod_cast abscissa_add_zero hn hR hV hRV
  · right;right;right
    constructor
    · have h := abscissa_add_T0 hn hQ hU hx hQU
      simpa only [commonSourceTranslateZero,Rat.cast_div,Rat.cast_neg,Rat.cast_pow] using
        congrArg (fun t : ℚ => (t:ℚ_[2])) h
    · have h := abscissa_add_T0 hn hR hV hw hRV
      simpa only [commonSourceTranslateZero,Rat.cast_div,Rat.cast_neg,Rat.cast_pow] using
        congrArg (fun t : ℚ => (t:ℚ_[2])) h

#print axioms actual_coordinate_orders_one
#print axioms actual_coordinate_orders_seven
end FourCorner.CommonSource
