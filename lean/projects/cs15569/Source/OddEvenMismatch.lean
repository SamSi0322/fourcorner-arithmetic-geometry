import ActualSurvivingOrders
import CSFoundation.CommonSourceOddLocalAssembly
import ReductionBridge

noncomputable section
namespace FourCorner.CommonSource
variable {q : ℕ} [Fact q.Prime]

/-- Mismatched even remainder disks in the n=1 case become the same nonzero
root disk after either surviving torsion order. -/
theorem even_mismatch_wrong_return_one (hq : q%8=5)
    {n x w a b c e : ℚ_[q]} (hn : ‖n‖=1) (hns : IsSquare n)
    (he : e ≠ 0) (hQ : b^2=a*(a-n)*(a+n)) (hR : e^2=c*(c-n)*(c+n))
    (hmismatch : (1 < ‖x‖ ∧ ‖w‖ < 1) ∨ (‖x‖ < 1 ∧ 1 < ‖w‖))
    (ho : (a=commonSourceTranslateMinus n x ∧ c=commonSourceTranslatePlus n w) ∨
      (a=commonSourceTranslatePlus n x ∧ c=commonSourceTranslateMinus n w)) :
    ¬ IsSquare (commonSourceReturn n a c) := by
  apply csOdd_not_isSquare_return_mismatched_disks hq hn hns he hQ hR
  have hq2 : q≠2 := by omega
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases hmismatch with ⟨hx,hw⟩ | ⟨hx,hw⟩
    · right;left
      exact ⟨(csOdd_torsion_disks_from_infinity hq2 hn hx).2.2,
        (csOdd_torsion_disks_from_zero hq2 hn hw).1⟩
    · left
      exact ⟨(csOdd_torsion_disks_from_zero hq2 hn hx).2,
        (csOdd_torsion_disks_from_infinity hq2 hn hw).2.1⟩
  · rcases hmismatch with ⟨hx,hw⟩ | ⟨hx,hw⟩
    · left
      exact ⟨(csOdd_torsion_disks_from_infinity hq2 hn hx).2.1,
        (csOdd_torsion_disks_from_zero hq2 hn hw).2⟩
    · right;left
      exact ⟨(csOdd_torsion_disks_from_zero hq2 hn hx).1,
        (csOdd_torsion_disks_from_infinity hq2 hn hw).2.2⟩

/-- Mismatched even remainder disks in the n=7 case remain opposite O/T0
disks, including every finite positive valuation depth. -/
theorem even_mismatch_wrong_return_seven (hq : q%8=5)
    {n x w a b c e : ℚ_[q]} (hn : ‖n‖=1) (hns : IsSquare n)
    (hx0 : x ≠ 0) (hw0 : w ≠ 0)
    (he : e ≠ 0) (hQ : b^2=a*(a-n)*(a+n)) (hR : e^2=c*(c-n)*(c+n))
    (hmismatch : (1 < ‖x‖ ∧ ‖w‖ < 1) ∨ (‖x‖ < 1 ∧ 1 < ‖w‖))
    (ho : (a=x ∧ c=w) ∨ (a=commonSourceTranslateZero n x ∧ c=commonSourceTranslateZero n w)) :
    ¬ IsSquare (commonSourceReturn n a c) := by
  apply csOdd_not_isSquare_return_mismatched_disks hq hn hns he hQ hR
  have hq2 : q≠2 := by omega
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inr (Or.inr hmismatch)
  · rcases hmismatch with ⟨hx,hw⟩ | ⟨hx,hw⟩
    · right;right;right
      exact ⟨(csOdd_torsion_disks_from_infinity hq2 hn hx).1,
        csOdd_torsion_zero_to_infinity hn hw hw0⟩
    · right;right;left
      exact ⟨csOdd_torsion_zero_to_infinity hn hx hx0,
        (csOdd_torsion_disks_from_infinity hq2 hn hw).1⟩

/-- Actual differing O/T0 reductions force opposite valuation disks for the
same rational finite points. This is not inferred from a list of representatives. -/
theorem actual_even_reduction_mismatch {n : ℤ}
    (hq2 : q≠2) (hnq : (n:ZMod q) ≠ 0) {x y w z : ℚ}
    (hU : CongruentEquation (n:ℚ) x y) (hV : CongruentEquation (n:ℚ) w z)
    (hu : reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hU)=0 ∨
      reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hU)=residueT0 n hnq)
    (hv : reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hV)=0 ∨
      reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hV)=residueT0 n hnq)
    (hne : reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hU) ≠
      reduce n hq2 hnq (finitePoint (rational_ne_zero_of_good hnq) hV)) :
    (1 < ‖(x:ℚ_[q])‖ ∧ ‖(w:ℚ_[q])‖ < 1) ∨
    (‖(x:ℚ_[q])‖ < 1 ∧ 1 < ‖(w:ℚ_[q])‖) := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact False.elim (hne (hu.trans hv.symm))
  · left
    exact ⟨(reduce_finitePoint_eq_zero_iff hq2 hnq hU).mp hu,
      (norm_lt_one_of_reduce_T0 hq2 hnq hV hv).1⟩
  · right
    exact ⟨(norm_lt_one_of_reduce_T0 hq2 hnq hU hu).1,
      (reduce_finitePoint_eq_zero_iff hq2 hnq hV).mp hv⟩
  · exact False.elim (hne (hu.trans hv.symm))

#print axioms even_mismatch_wrong_return_one
#print axioms even_mismatch_wrong_return_seven
#print axioms actual_even_reduction_mismatch
end FourCorner.CommonSource
