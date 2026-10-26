import HpGoodLocal
import HpOddPoleLocal

namespace FourCorner.HpOddSourceOpen
open HpResidueCharts HpHenselOrdinary PadicUnitNeighbourhood HasseNorms HilbertArithmeticHigh11
noncomputable section

/-- Every strict original odd-adic source point has a nearby source point
whose parameter is Q-transcendental. Radicands are divided by their actual
nonzero initial squares before simultaneous unit Hensel. -/
theorem transcendental_source (Q : OddPrime) (p : ℚ) (S : LocalPoint ℚ_[Q.val] (p : ℚ_[Q.val])) :
    ∃S' : LocalPoint ℚ_[Q.val] (p : ℚ_[Q.val]),Transcendental ℚ S'.rho := by
  let R : Fin 4 → ℚ_[Q.val] := ![S.u,S.v,S.w,S.t]
  have hR (i : Fin 4) : R i ≠ 0 := by
    fin_cases i
    · exact S.u_ne_zero
    · exact S.v_ne_zero
    · exact S.w_ne_zero
    · exact S.t_ne_zero
  have hRs (i : Fin 4) : R i^2=values (p : ℚ_[Q.val]) S.rho i := by
    fin_cases i
    · exact S.sqU
    · exact S.sqV
    · exact S.sqW
    · exact S.sqT
  let f (i : Fin 4) (e : ℚ_[Q.val]) := values (p : ℚ_[Q.val]) e i/(R i)^2
  obtain ⟨e,he,hr⟩ := transcendental_simultaneous_roots Q.property.2 f S.rho (fun _ => 1)
    (fun i => (continuous_values _ i).continuousAt.div_const _)
    (fun i => by dsimp [f];rw [← hRs];exact div_self (pow_ne_zero _ (hR i)))
    (fun _ => by rw [map_one];exact one_ne_zero)
    (fun _ => by rw [map_one];exact IsSquare.one)
  choose z hz hs using hr
  let r (i : Fin 4) := R i*z i
  have hr0 (i : Fin 4) : r i ≠ 0 := mul_ne_zero (hR i) (hz i)
  have hrs (i : Fin 4) : r i^2=values (p : ℚ_[Q.val]) e i := by
    dsimp [r]
    rw [mul_pow,hs]
    dsimp [f]
    field_simp [hR i]
  exact ⟨toLocalPoint p e he r hr0 hrs,he⟩

/-- Every displayed parameter has an actual odd-adic source point at
all q≥101. Bad reduction is treated by explicit witnesses; good reduction
uses actual genus-five Hasse-Weil and exhaustive place charts. -/
theorem family_large (Q : OddPrime) (hlarge : 101≤Q.val) (j : ℕ) :
    ∃S : LocalPoint ℚ_[Q.val] (HpInfiniteArithmetic.p j : ℚ_[Q.val]),Transcendental ℚ S.rho := by
  let p := HpInfiniteArithmetic.p j
  let r := HpInfiniteArithmetic.r j
  let s := HpInfiniteArithmetic.s j
  have hp : 1<p := HpInfiniteArithmetic.p_gt_one j
  have hr : r^2=2*(p+1) := HpInfiniteArithmetic.r_square j
  have hr0 : r ≠ 0 := HpInfiniteArithmetic.anchor_nonzero j
  have hs : s^2=3-p := by dsimp [s,p,HpInfiniteArithmetic.p];ring
  have hs0 : s ≠ 0 := ne_of_lt (HpInfiniteArithmetic.s_negative j)
  by_cases hv : padicValRat Q.val p<0
  · obtain ⟨S⟩ := HpOddPoleLocal.pole Q p s hp hs hv
    exact transcendental_source Q p S
  · have hpv : 0≤(p : ℚ_[Q.val]).valuation := by rw [Padic.valuation_ratCast];omega
    let P : ℤ_[Q.val] := ⟨(p : ℚ_[Q.val]),(Padic.norm_le_one_iff_val_nonneg _).mpr hpv⟩
    have hP : (P : ℚ_[Q.val])=(p : ℚ_[Q.val]) := rfl
    have pos_of_residue (x : ℤ_[Q.val]) (hx : (x : ℚ_[Q.val]) ≠ 0) (hz : PadicInt.toZMod x=0) :
        0<(x : ℚ_[Q.val]).valuation :=
      (commonRoot_norm_lt_one_iff hx).mp ((padicInt_norm_lt_one_iff_residue_zero x).mpr hz)
    by_cases hP0 : PadicInt.toZMod P=0
    · have hp0 : (P : ℚ_[Q.val]) ≠ 0 := by rw [hP];exact_mod_cast (show p ≠ 0 by linarith)
      have hh := pos_of_residue P hp0 hP0
      rw [hP,Padic.valuation_ratCast] at hh
      obtain ⟨S⟩ := HpOddBadLocal.positive_p Q p r hp hr hh
      exact transcendental_source Q p S
    by_cases hPa : PadicInt.toZMod P-1=0
    · have ha0 : ((P-1 : ℤ_[Q.val]) : ℚ_[Q.val]) ≠ 0 := by
        rw [PadicInt.coe_sub,PadicInt.coe_one,hP]
        exact_mod_cast (show p-1 ≠ 0 by linarith)
      have hh := pos_of_residue (P-1) ha0 (by simpa only [map_sub,map_one] using hPa)
      have hh' : 0<padicValRat Q.val (p-1) := by
        have he : ((P-1 : ℤ_[Q.val]) : ℚ_[Q.val])=((p-1 : ℚ) : ℚ_[Q.val]) := by
          rw [PadicInt.coe_sub,PadicInt.coe_one,hP];push_cast;rfl
        rwa [he,Padic.valuation_ratCast] at hh
      obtain ⟨S⟩ := HpOddBadLocal.positive_a Q p s hp hs hs0 hh'
      exact transcendental_source Q p S
    by_cases hPb : PadicInt.toZMod P+1=0
    · have hb0 : ((P+1 : ℤ_[Q.val]) : ℚ_[Q.val]) ≠ 0 := by
        rw [PadicInt.coe_add,PadicInt.coe_one,hP]
        exact_mod_cast (show p+1 ≠ 0 by linarith)
      have hh := pos_of_residue (P+1) hb0 (by simpa only [map_add,map_one] using hPb)
      rw [PadicInt.coe_add,PadicInt.coe_one,hP] at hh
      obtain ⟨S⟩ := HpOddMoreLocal.positive_b Q p hp r hr hr0 hh
      exact transcendental_source Q p S
    exact HpGoodLocal.large_good_prime Q.property.2 hlarge p hp P hP hP0 hPa hPb

#print axioms transcendental_source
#print axioms family_large
end
end FourCorner.HpOddSourceOpen
