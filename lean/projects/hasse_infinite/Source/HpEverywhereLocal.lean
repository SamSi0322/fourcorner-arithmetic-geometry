import HpSmallLocal
import HpStrictRealGeneric
import HpDyadicSourceOpen

namespace FourCorner.HpEverywhereLocal
open CategoryTheory HasseNorms HilbertArithmeticHigh11 HpOddSourceOpen
noncomputable section

/-- Every odd prime, including all small ordinary residues and all
positive or negative parameter valuation depths. -/
theorem family_odd (Q : OddPrime) (j : ℕ) :
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
    by_cases hlarge : 101≤Q.val
    · exact HpGoodLocal.large_good_prime Q.property.2 hlarge p hp P hP hP0 hPa hPb
    · exact HpSmallLocal.family_small_good Q.property.2 (by omega) j P hP hP0 hPa hPb

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem family_two (j : ℕ) :
    Nonempty (LocalPoint ℚ_[2] (HpInfiniteArithmetic.p j : ℚ_[2])) := by
  apply HpDyadicFamilyPoint.local_point_at_two _ (HpInfiniteArithmetic.p_gt_one j)
    (HpInfiniteArithmetic.r j) (HpInfiniteArithmetic.r_square j) (HpInfiniteArithmetic.anchor_nonzero j)
  have he : ((HpInfiniteArithmetic.p j : ℚ_[2])+1).valuation=5 := by
    have hh : (HpInfiniteArithmetic.p j : ℚ_[2])+1=((HpInfiniteArithmetic.p j+1 : ℚ) : ℚ_[2]) := by push_cast;rfl
    rw [hh,Padic.valuation_ratCast]
    exact HpFamilyDyadicValuation.b_valuation j
  omega

/-- Unconditional everywhere local solubility of the EXACT displayed family.
All finite primes, the real place, and every strict original source guard
are present, independently of the previously proved rational exclusion. -/
theorem family_Loc (j : ℕ) : Loc (HpInfiniteArithmetic.p j) := by
  refine ⟨?_,?_⟩
  · obtain ⟨S,_,_,_⟩ := HpStrictRealGeneric.family_strict_real_transcendental j
    exact ⟨S⟩
  · intro q hq
    by_cases h2 : q=2
    · subst q;exact family_two j
    · let Q : OddPrime := ⟨q,hq.out,h2⟩
      obtain ⟨S,_⟩ := family_odd Q j
      exact ⟨S⟩

theorem family_odd_model_point (Q : OddPrime) (j : ℕ) :
    ∃f : AlgebraicGeometry.Spec (CommRingCat.of ℚ_[Q.val]) ⟶ HpSchemeModel.curve (HpInfiniteArithmetic.p j),
      f ≫ HpSchemeModel.toBase (HpInfiniteArithmetic.p j)=
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[Q.val])) := by
  obtain ⟨S,htrans⟩ := family_odd Q j
  let r : Fin 4 → ℚ_[Q.val] := ![S.u,S.v,S.w,S.t]
  have hr (i : Fin 4) : r i^2=HpResidueCharts.values (HpInfiniteArithmetic.p j : ℚ_[Q.val]) S.rho i := by
    fin_cases i
    · exact S.sqU
    · exact S.sqV
    · exact S.sqW
    · exact S.sqT
  exact ⟨HpModelFieldPoint.point _ (HpInfiniteArithmetic.p_gt_one j) S.rho htrans r hr,
    HpModelFieldPoint.point_overQ _ (HpInfiniteArithmetic.p_gt_one j) S.rho htrans r hr⟩

/-- Actual points on the same smooth proper model at EVERY finite place. -/
theorem family_model_point (q : ℕ) [Fact q.Prime] (j : ℕ) :
    ∃f : AlgebraicGeometry.Spec (CommRingCat.of ℚ_[q]) ⟶ HpSchemeModel.curve (HpInfiniteArithmetic.p j),
      f ≫ HpSchemeModel.toBase (HpInfiniteArithmetic.p j)=
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[q])) := by
  by_cases h2 : q=2
  · subst q
    obtain ⟨S⟩ := family_two j
    obtain ⟨S,htrans⟩ := HpDyadicSourceOpen.transcendental_source _ S
    let r : Fin 4 → ℚ_[2] := ![S.u,S.v,S.w,S.t]
    have hr (i : Fin 4) : r i^2=HpResidueCharts.values (HpInfiniteArithmetic.p j : ℚ_[2]) S.rho i := by
      fin_cases i
      · exact S.sqU
      · exact S.sqV
      · exact S.sqW
      · exact S.sqT
    exact ⟨HpModelFieldPoint.point _ (HpInfiniteArithmetic.p_gt_one j) S.rho htrans r hr,
      HpModelFieldPoint.point_overQ _ (HpInfiniteArithmetic.p_gt_one j) S.rho htrans r hr⟩
  · exact family_odd_model_point ⟨q,Fact.out,h2⟩ j

#print axioms family_odd
#print axioms family_Loc
#print axioms family_odd_model_point
#print axioms family_model_point
end
end FourCorner.HpEverywhereLocal
