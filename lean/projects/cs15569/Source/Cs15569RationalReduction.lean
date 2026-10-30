import Cs15569DyadicGeneration
import ReductionBridge
import CSFoundation.CommonSourceOddLocalResidue

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section
variable {q : ℕ} [Fact q.Prime]

/-- Actual rational integral coordinates and their residue are computed from
an exact integer fraction with a unit denominator. -/
theorem rational_fraction_reduction (r : ℚ) (a b : ℤ)
    (hb : (b : ZMod q) ≠ 0) (hr : r=(a : ℚ)/(b : ℚ)) :
    ∃ hx : (primeIdeal q).valuation ℚ r≤1,
      PadicInt.toZMod (rationalIntegral q r hx)=(a : ZMod q)/(b : ZMod q) := by
  have hbpad : PadicInt.toZMod (b : ℤ_[q]) ≠ 0 := by simpa only [map_intCast] using hb
  have hbnorm : ‖(b : ℚ_[q])‖=1 := padicInt_norm_coe_eq_one_of_residue_ne_zero (b : ℤ_[q]) hbpad
  have hb0 : (b : ℚ_[q]) ≠ 0 := by intro hz; rw [hz,norm_zero] at hbnorm; norm_num at hbnorm
  have hr' : (r : ℚ_[q])=(a : ℚ_[q])/(b : ℚ_[q]) := by exact_mod_cast hr
  have hnorm : ‖(r : ℚ_[q])‖≤1 := by
    rw [hr',norm_div,hbnorm,div_one]
    exact Padic.norm_int_le_one a
  let hx := (valuation_le_one_iff_norm q r).mpr hnorm
  refine ⟨hx,?_⟩
  have heq : rationalIntegral q r hx*(b : ℤ_[q])=(a : ℤ_[q]) := by
    apply PadicInt.ext
    push_cast
    rw [rationalIntegral_coe,hr',div_mul_cancel₀ _ hb0]
  have he := congrArg (PadicInt.toZMod : ℤ_[q] →+* ZMod q) heq
  simp only [map_mul,map_intCast] at he
  exact (eq_div_iff hb).mpr he

/-- Both coordinates come from the same actual rational finite point. -/
theorem reduction_fraction_coordinates (hq2 : q ≠ 2) (hnq : ((15569 : ℤ) : ZMod q) ≠ 0)
    {x y : ℚ} (hE : CongruentEquation 15569 x y)
    (a b c d : ℤ) (hb : (b : ZMod q) ≠ 0) (hd : (d : ZMod q) ≠ 0)
    (hx : x=(a : ℚ)/(b : ℚ)) (hy : y=(c : ℚ)/(d : ℚ)) :
    residueCoordinates (reduce 15569 hq2 hnq (finitePoint (by norm_num) hE))=
      some ((a : ZMod q)/(b : ZMod q),(c : ZMod q)/(d : ZMod q)) := by
  obtain ⟨hxi,hxr⟩ := rational_fraction_reduction x a b hb hx
  obtain ⟨hyi,hyr⟩ := rational_fraction_reduction y c d hd hy
  rw [reduce_finitePoint_padic_coordinates hq2 hnq hE hxi,hxr,hyr]

/-- Exact reductions of P, with a proved denominator-unit condition at q. -/
theorem P_reduction_coordinates (hq2 : q ≠ 2) (hnq : ((15569 : ℤ) : ZMod q) ≠ 0)
    (hd : (7760 : ZMod q) ≠ 0) :
    residueCoordinates (reduce 15569 hq2 hnq P)=
      some ((15569*7809^2/7760^2 : ZMod q),
        (-(15569*7809*108983*11009)/7760^3 : ZMod q)) := by
  unfold P
  convert reduction_fraction_coordinates hq2 hnq Cs15569Finite.p_on_curve
    (15569*7809^2) (7760^2) (-(15569*7809*108983*11009)) (7760^3)
    (by simpa only [Int.cast_pow,Int.cast_ofNat] using pow_ne_zero 2 hd)
    (by simpa only [Int.cast_pow,Int.cast_ofNat] using pow_ne_zero 3 hd)
    (by norm_num [Cs15569Finite.px]) (by norm_num [Cs15569Finite.py]) using 1 <;> push_cast <;> norm_num

theorem G_reduction_coordinates (hq2 : q ≠ 2) (hnq : ((15569 : ℤ) : ZMod q) ≠ 0)
    (hd : (13382920 : ZMod q) ≠ 0) :
    residueCoordinates (reduce 15569 hq2 hnq G)=
      some ((15569*13522049^2/13382920^2 : ZMod q),
        (-(15569*13522049*1934751*2373852137)/13382920^3 : ZMod q)) := by
  unfold G
  convert reduction_fraction_coordinates hq2 hnq Cs15569Finite.g_on_curve
    (15569*13522049^2) (13382920^2) (-(15569*13522049*1934751*2373852137)) (13382920^3)
    (by simpa only [Int.cast_pow,Int.cast_ofNat] using pow_ne_zero 2 hd)
    (by simpa only [Int.cast_pow,Int.cast_ofNat] using pow_ne_zero 3 hd)
    (by norm_num [Cs15569Finite.gx]) (by norm_num [Cs15569Finite.gy]) using 1 <;> push_cast <;> norm_num

#print axioms rational_fraction_reduction
#print axioms reduction_fraction_coordinates
#print axioms P_reduction_coordinates
#print axioms G_reduction_coordinates
end
end FourCorner.Cs15569Completion
