import HasseInertParity

namespace FourCorner.HasseWR

open HasseRationalSource HasseAnchorChoice HasseObstructionArithmetic HasseParameterSupport
open HasseInertParity HasseSignAlgebra HasseTwoSymbol HasseHilbertArithmetic
open HilbertArithmeticHigh11 HilbertWellDefinedHigh11

def ratio (p : ℚ) (P : HomogeneousPoint p) (D : TangentData p P) : ℚ := D.w/P.Z

theorem ratio_ne_zero (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P) :
    ratio p P D ≠ 0 := by
  have hh := coordinates_ne_zero p hp P
  have hw : D.w ≠ 0 := by rcases D.sign with h | h <;> rw [h] <;> simpa using hh.2.2.2.1
  exact div_ne_zero hw hh.1

noncomputable def wSign (p : ℚ) (hp : 1<p) (P : HomogeneousPoint p) (D : TangentData p P) (v : ℕ) : ℤ :=
  rationalSign 2 (ratio p P D) (by norm_num) (ratio_ne_zero p hp P D) v

noncomputable def positiveTerm (r : ℚ) (q : ℕ) : ZMod 2 := by
  classical
  exact if q≠2 ∧ ¬IsSquare (2 : ZMod q) ∧ 0<padicValRat q r then (padicValRat q r/2 : ℤ) else 0

noncomputable def inertTerm (r : ℚ) (q : ℕ) : ZMod 2 := by
  classical
  exact if q≠2 ∧ ¬IsSquare (2 : ZMod q) then (padicValRat q r : ZMod 2) else 0

theorem halfInertSum_on_parameter_support (p r : ℚ) (hr : r ≠ 0)
    (hsub : rationalSupport r ⊆ parameterSupport p) :
    halfInertSum r=∑ q ∈ oddParameterSupport p,positiveTerm r q := by
  classical
  let F := (rationalSupport r).filter (fun q => q≠2 ∧ ¬IsSquare (2 : ZMod q) ∧ 0<padicValRat q r)
  have hF : F ⊆ oddParameterSupport p := by
    intro q hq
    have hh := Finset.mem_filter.mp hq
    have hprime := prime_of_rationalSupport r q hh.1
    simp only [oddParameterSupport,Finset.mem_erase]
    exact ⟨hh.2.1,hprime.ne_zero,hsub hh.1⟩
  have he : halfInertSum r=∑ q ∈ F,positiveTerm r q := by
    change (∑ q ∈ F,((padicValRat q r/2 : ℤ) : ZMod 2))= _
    apply Finset.sum_congr rfl
    intro q hq
    have hh := (Finset.mem_filter.mp hq).2
    simp only [positiveTerm,if_pos hh]
  rw [he]
  apply Finset.sum_subset hF
  intro q hq hn
  by_cases hc : q≠2 ∧ ¬IsSquare (2 : ZMod q) ∧ 0<padicValRat q r
  · have hnot : q∉rationalSupport r := by
      intro hh
      exact hn (Finset.mem_filter.mpr ⟨hh,hc⟩)
    have hpq := (oddParameterSupport_prime p q hq).1
    have hv := valuation_zero_outside_support r hr q hpq hnot
    exact False.elim (by rw [hv] at hc; omega)
  · simp only [positiveTerm,if_neg hc]

theorem source_inert_sum (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    (∑ q ∈ oddParameterSupport p,inertTerm (ratio p P D) q)=A p+B p := by
  classical
  have ha : halfInertSum (p-1)=∑ q ∈ oddParameterSupport p,positiveTerm (p-1) q :=
    halfInertSum_on_parameter_support p (p-1) (by linarith) (by intro q hq; simp [parameterSupport,hq])
  have hb : halfInertSum (p+1)=∑ q ∈ oddParameterSupport p,positiveTerm (p+1) q :=
    halfInertSum_on_parameter_support p (p+1) (by linarith) (by intro q hq; simp [parameterSupport,hq])
  change _=halfInertSum (p-1)+halfInertSum (p+1)
  rw [ha,hb,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hqprime,hq2⟩ := oddParameterSupport_prime p q hq
  let Q : OddPrime := ⟨q,hqprime,hq2⟩
  by_cases h2 : IsSquare (2 : ZMod q)
  · simp only [inertTerm,positiveTerm,h2,not_true_eq_false,and_false,false_and,if_false,zero_add]
  · have hh := source_support_bit Q p hp hL P D h2
    simpa [inertTerm,positiveTerm,ratio,positiveHalf,hq2,h2,Q] using hh

theorem wSign_odd_product (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    (∏ q ∈ oddParameterSupport p,wSign p hp P D q)=bitSign (A p+B p) := by
  classical
  rw [← source_inert_sum p hp hL P D,bitSign_sum]
  apply Finset.prod_congr rfl
  intro q hq
  obtain ⟨hqprime,hq2⟩ := oddParameterSupport_prime p q hq
  let Q : OddPrime := ⟨q,hqprime,hq2⟩
  have hh := rationalSign_two_odd Q (ratio p P D) (ratio_ne_zero p hp P D)
  by_cases h2 : IsSquare (2 : ZMod q)
  · simpa [wSign,inertTerm,h2,Q,bitSign_zero] using hh
  · simpa [wSign,inertTerm,h2,hq2,Q] using hh

theorem wSign_one_outside_parameter_support (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) (q : ℕ) (h : q∉parameterSupport p) :
    wSign p hp P D q=1 := by
  classical
  have hs : q≠0 ∧ q≠2 ∧ q∉rationalSupport p ∧ q∉rationalSupport (p-1) ∧ q∉rationalSupport (p+1) := by
    simpa only [parameterSupport,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or,and_assoc] using h
  by_cases hq : q.Prime
  · letI : Fact q.Prime := ⟨hq⟩
    let Q : OddPrime := ⟨q,hq,hs.2.1⟩
    rw [wSign,rationalSign_two_odd Q]
    by_cases h2 : IsSquare (2 : ZMod q)
    · rw [if_pos h2]
    · rw [if_neg h2]
      have hh := (HasseInertSupport.source_support Q p hp P D
        (SqrtTwoGlobalNorm.nonsquare_two_completion h2)).2
      change 2*padicValRat q (D.w/P.Z)=padicValRat q (p+1)-padicValRat q (p-1) at hh
      rw [valuation_zero_outside_support (p-1) (by linarith) q hq hs.2.2.2.1,
        valuation_zero_outside_support (p+1) (by linarith) q hq hs.2.2.2.2] at hh
      have hv : padicValRat q (ratio p P D)=0 := by dsimp [ratio]; omega
      rw [hv,Int.cast_zero,bitSign_zero]
  · exact rationalSign_one_of_not_prime _ _ _ _ q hs.1 hs.2.1 hq

theorem wSign_parameter_product (p : ℚ) (hp : 1<p)
    (P : HomogeneousPoint p) (D : TangentData p P) :
    (∏ v ∈ parameterSupport p,wSign p hp P D v)=1 := by
  let S := {0,2} ∪ rationalSupport 2 ∪ rationalSupport (ratio p P D)
  let U := parameterSupport p
  have hglob : (∏ v ∈ S,wSign p hp P D v)=1 := rational_reciprocity_on_rational_support _ _ _ _
  have hleft : (∏ v ∈ S ∪ U,wSign p hp P D v)=(∏ v ∈ S,wSign p hp P D v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_left
    intro v hv hn
    exact rationalSign_one_outside_rational_support _ _ _ _ v hn
  have hright : (∏ v ∈ S ∪ U,wSign p hp P D v)=(∏ v ∈ U,wSign p hp P D v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_right
    intro v hv hn
    exact wSign_one_outside_parameter_support p hp P D v hn
  exact hright.symm.trans (hleft.trans hglob)

/-- Exact eq:hp-WR for the literal rational anchor ratio. Its global
reciprocity, finite support and every inert valuation are all proved. -/
theorem global_wsupport (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (P : HomogeneousPoint p) (D : TangentData p P) : wSign p hp P D 2=bitSign (A p+B p) := by
  have h0 : 0∈parameterSupport p := by simp [parameterSupport]
  have h2 : 2∈(parameterSupport p).erase 0 := by simp [parameterSupport]
  have he := Finset.mul_prod_erase (parameterSupport p) (wSign p hp P D) h0
  have he2 := Finset.mul_prod_erase ((parameterSupport p).erase 0) (wSign p hp P D) h2
  have hr : wSign p hp P D 0=1 := rationalSign_two_real _ _
  rw [hr,one_mul,wSign_parameter_product] at he
  have hprod : wSign p hp P D 2*bitSign (A p+B p)=1 := by
    have hh := he2.trans he
    change wSign p hp P D 2*(∏ q ∈ oddParameterSupport p,wSign p hp P D q)=1 at hh
    rwa [wSign_odd_product p hp hL P D] at hh
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hprod with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;> rw [hx,hy]

#print axioms source_inert_sum
#print axioms wSign_odd_product
#print axioms wSign_parameter_product
#print axioms global_wsupport

end FourCorner.HasseWR
