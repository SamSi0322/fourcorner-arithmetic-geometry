import Cs15569DyadicUnit
import RationalCosets15569

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

private theorem rational_sum_dominant {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : padicValRat 2 a<padicValRat 2 b) :
    a+b ≠ 0 ∧ padicValRat 2 (a+b)=padicValRat 2 a := by
  have hab : a+b ≠ 0 := by
    intro hz
    have he : a= -b := eq_neg_of_add_eq_zero_left hz
    have hh := congrArg (padicValRat 2) he
    rw [padicValRat.neg] at hh
    omega
  exact ⟨hab,padicValRat.add_eq_of_lt hab ha hb hv⟩

private theorem equation_of_coordinates (Q : E) {x y : ℚ}
    (hQ : coordinates Q=some (x,y)) : CongruentEquation 15569 x y := by
  cases Q with
  | zero => cases hQ
  | some a b he =>
    simp only [coordinates,Option.some.injEq,Prod.mk.injEq] at hQ
    rcases hQ with ⟨rfl,rfl⟩
    exact (congruentEquation_iff_weierstrass _ _ _).mpr he.1

private theorem H_of_negative_coordinates (Q : E) {x y : ℚ}
    (hQ : coordinates Q=some (x,y)) (hv : padicValRat 2 x<0) :
    Q ∈ H 15569 (by norm_num) := by
  have heq := equation_of_coordinates Q hQ
  have hvd := negative_valuation_deep heq hv
  cases Q with
  | zero => cases hQ
  | some a b he =>
    simp only [coordinates,Option.some.injEq,Prod.mk.injEq] at hQ
    rcases hQ with ⟨rfl,rfl⟩
    exact (some_mem_H_iff 15569 (by norm_num) a b he).mpr hvd

private theorem translated_decomposition (Q t : E) (ht : 2 • t=0)
    (hh : Q+t ∈ H 15569 (by norm_num)) :
    ∃ h ∈ H 15569 (by norm_num), ∃ τ : E, 2 • τ=0 ∧ Q=h+τ := by
  refine ⟨Q+t,hh,t,ht,?_⟩
  have htt : t+t=0 := by simpa only [two_nsmul] using ht
  calc
    Q = Q+(t+t) := by rw [htt,add_zero]
    _ = (Q+t)+t := by abel

private theorem plus_translation_negative {x : ℚ} (hm : x-15569 ≠ 0)
    (hv : 3≤padicValRat 2 (x-15569)) :
    padicValRat 2 (15569+2*15569^2/(x-15569))<0 := by
  have hn : (15569 : ℚ) ≠ 0 := by norm_num
  have hnum : (2*15569^2 : ℚ) ≠ 0 := by norm_num
  have hterm : padicValRat 2 (2*15569^2/(x-15569))=1-padicValRat 2 (x-15569) := by
    rw [padicValRat.div hnum hm,padicValRat.mul (by norm_num) (pow_ne_zero _ hn),
      padicValRat.pow,val_n_two]
    have htwo : padicValRat 2 (2 : ℚ)=1 := by simpa only [Nat.cast_ofNat] using padicValRat.self (p:=2) (by norm_num)
    rw [htwo]
    norm_num
  have hs := rational_sum_dominant (div_ne_zero hnum hm) hn
    (by rw [hterm,val_n_two]; omega)
  rw [add_comm,hs.2,hterm]
  omega

private theorem minus_translation_negative {x : ℚ} (hp : x+15569 ≠ 0)
    (hv : 3≤padicValRat 2 (x+15569)) :
    padicValRat 2 (-15569+2*15569^2/(x+15569))<0 := by
  have hn : (15569 : ℚ) ≠ 0 := by norm_num
  have hnum : (2*15569^2 : ℚ) ≠ 0 := by norm_num
  have hterm : padicValRat 2 (2*15569^2/(x+15569))=1-padicValRat 2 (x+15569) := by
    rw [padicValRat.div hnum hp,padicValRat.mul (by norm_num) (pow_ne_zero _ hn),
      padicValRat.pow,val_n_two]
    have htwo : padicValRat 2 (2 : ℚ)=1 := by simpa only [Nat.cast_ofNat] using padicValRat.self (p:=2) (by norm_num)
    rw [htwo]
    norm_num
  have hneg : padicValRat 2 (-15569 : ℚ)=0 := by simpa only [padicValRat.neg] using val_n_two
  have hs := rational_sum_dominant (div_ne_zero hnum hp) (neg_ne_zero.mpr hn)
    (by rw [hterm,hneg]; omega)
  rw [add_comm,hs.2,hterm]
  omega

/-- Constructive exhaustive dyadic splitting for every actual rational point.
Infinity and every two-torsion point are handled before the ordinary cases.
The ordinary cases are v2(x)<0, =0, >0, all at unbounded depth. -/
theorem actual_dyadic_splitting : SplitsOverTwoTorsion 15569 (H 15569 (by norm_num)) := by
  intro Q
  by_cases htwo : 2 • Q=0
  · exact ⟨0,(H 15569 (by norm_num)).zero_mem,Q,htwo,by simp⟩
  cases Q with
  | zero => exact False.elim (htwo (by change 2 • (0 : E)=0; simp))
  | some x y he =>
    have hE : CongruentEquation 15569 x y :=
      (congruentEquation_iff_weierstrass _ _ _).mpr he.1
    have hy : y ≠ 0 := by
      intro hy
      apply htwo
      rw [two_nsmul]
      apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
      simp [WeierstrassCurve.Affine.negY,congruentCurve,WeierstrassCurve.toAffine,hy]
    have hprod : x*(x-15569)*(x+15569) ≠ 0 := by
      rw [←hE]
      exact pow_ne_zero _ hy
    have hx : x ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).1
    have hm : x-15569 ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).2
    have hp : x+15569 ≠ 0 := (mul_ne_zero_iff.mp hprod).2
    have hfinite : (.some x y he : E)=finitePoint (by norm_num) hE := rfl
    rcases lt_trichotomy (padicValRat 2 x) 0 with hv | hv | hv
    · refine ⟨.some x y he,?_,0,by simp,by simp⟩
      exact (some_mem_H_iff 15569 (by norm_num) x y he).mpr (negative_valuation_deep hE hv)
    · rcases unit_offset_deep hE hx hm hp hv with hvm | hvp
      · apply translated_decomposition (.some x y he) (Tplus 15569 (by norm_num))
          (by rw [two_nsmul,Tplus_add_self])
        apply H_of_negative_coordinates _ (x:=15569+2*15569^2/(x-15569))
          (y:= -(2*15569^2*y)/(x-15569)^2)
        · rw [hfinite]
          exact coordinates_add_Tplus (by norm_num) hE (by intro hh; apply hm; simp [hh])
        · exact plus_translation_negative hm hvm
      · apply translated_decomposition (.some x y he) (Tminus 15569 (by norm_num))
          (by rw [two_nsmul,Tminus_add_self])
        apply H_of_negative_coordinates _ (x:= -15569+2*15569^2/(x+15569))
          (y:= -(2*15569^2*y)/(x+15569)^2)
        · rw [hfinite]
          exact coordinates_add_Tminus (by norm_num) hE (by intro hh; apply hp; simp [hh])
        · exact minus_translation_negative hp hvp
    · apply translated_decomposition (.some x y he) (T0 15569 (by norm_num))
        (by rw [two_nsmul,T0_add_self])
      apply H_of_negative_coordinates _ (x:= -(15569 : ℚ)^2/x) (y:=15569^2*y/x^2)
      · rw [hfinite]
        exact coordinates_add_T0 (by norm_num) hE hx
      · rw [padicValRat.div (by norm_num) hx,padicValRat.neg,padicValRat.pow,val_n_two]
        norm_num
        omega

/-- The splitting is direct: the actual dyadic H has no nonzero rational
point killed by two. This uses the proven local Kummer kernel on torsion. -/
theorem actual_dyadic_direct_sum : IsCompl (H 15569 (by norm_num)) (twoTorsion 15569) := by
  rw [isCompl_iff]
  constructor
  · rw [AddSubgroup.disjoint_def]
    intro Q hQ ht
    apply localKummer_twoTorsion_kernel 15569 (by norm_num) Q ht
    exact localKummer_H 15569 (by norm_num) Q hQ
  · rw [codisjoint_iff]
    apply top_unique
    intro Q _
    obtain ⟨h,hh,t,ht,hQ⟩ := actual_dyadic_splitting Q
    apply AddSubgroup.mem_sup.mpr
    exact ⟨h,hh,t,ht,hQ.symm⟩

/-- Every actual ambient rational halving witness can now be compensated by
a genuine rational two-torsion point so that it lies in the entire H. -/
theorem actual_H_halving {Q : E} (hh : ∃ R : E, 2 • R=Q) :
    ∃ Z ∈ H 15569 (by norm_num), 2 • Z=Q :=
  exists_double_in_subgroup actual_dyadic_splitting hh

#print axioms actual_dyadic_splitting
#print axioms actual_dyadic_direct_sum
#print axioms actual_H_halving
end
end FourCorner.Cs15569Completion
