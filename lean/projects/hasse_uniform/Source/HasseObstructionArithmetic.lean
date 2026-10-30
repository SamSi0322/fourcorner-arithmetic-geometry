import HasseAnchorChoice

/-! Literal finite arithmetic obstruction from §05. These are exact definitions
and well-definedness/support proofs, not an obstruction or no-point theorem. -/
namespace FourCorner.HasseObstructionArithmetic

open scoped BigOperators

/-- A finite set containing exactly the possible finite-prime support of a
nonzero rational. Both numerator and denominator primes are retained. -/
def rationalSupport (r : ℚ) : Finset ℕ := r.num.natAbs.primeFactors ∪ r.den.primeFactors

theorem valuation_zero_outside_support (r : ℚ) (hr : r ≠ 0) (q : ℕ)
    (hq : q.Prime) (h : q ∉ rationalSupport r) : padicValRat q r=0 := by
  have hn : ¬ q ∣ r.num.natAbs := by
    intro hd
    apply h
    exact Finset.mem_union_left _ (hq.mem_primeFactors hd (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hr)))
  have hd : ¬ q ∣ r.den := by
    intro hd
    apply h
    exact Finset.mem_union_right _ (hq.mem_primeFactors hd r.den_ne_zero)
  rw [padicValRat_def,padicValInt,padicValNat.eq_zero_of_not_dvd hn,
    padicValNat.eq_zero_of_not_dvd hd]
  rfl

theorem mem_support_of_valuation_ne_zero (r : ℚ) (hr : r ≠ 0) (q : ℕ)
    (hq : q.Prime) (hv : padicValRat q r ≠ 0) : q ∈ rationalSupport r := by
  by_contra hh
  exact hv (valuation_zero_outside_support r hr q hq hh)

noncomputable def halfInertSum (r : ℚ) : ZMod 2 := by
  classical
  exact ∑ q ∈ (rationalSupport r).filter (fun q => q ≠ 2 ∧
    ¬ IsSquare (2 : ZMod q) ∧ 0 < padicValRat q r),
      ((padicValRat q r / 2 : ℤ) : ZMod 2)

noncomputable def A (p : ℚ) : ZMod 2 := halfInertSum (p-1)
noncomputable def B (p : ℚ) : ZMod 2 := halfInertSum (p+1)

noncomputable def rootTwo (q : ℕ) : ZMod q := by
  classical
  exact if h : IsSquare (2 : ZMod q) then Classical.choose h else 0

theorem rootTwo_sq (q : ℕ) (h : IsSquare (2 : ZMod q)) : (rootTwo q)^2=2 := by
  classical
  simp only [rootTwo,dif_pos h,pow_two]
  exact (Classical.choose_spec h).symm

noncomputable def bitAtRoot {F : Type*} [Field F] (e : F) : ZMod 2 := by
  classical
  exact if IsSquare (2+e) then 0 else 1

private theorem two_add_root_ne_zero {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (e : F) (he : e^2=2) : 2+e ≠ 0 := by
  intro hh
  have he' : e= -2 := by linear_combination hh
  rw [he'] at he
  apply h2
  linear_combination he

/-- Root-sign independence in the paper is an exact squareclass statement,
proved here over every field of characteristic different from two. -/
theorem squareclass_root_sign {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (e : F) (he : e^2=2) : IsSquare (2+e) ↔ IsSquare (2-e) := by
  have hp : 2+e ≠ 0 := two_add_root_ne_zero h2 e he
  have hm : 2-e ≠ 0 := by
    simpa only [sub_eq_add_neg] using
      (two_add_root_ne_zero h2 (-e) (by simpa only [neg_sq] using he))
  have hprod : (2+e)*(2-e)=e^2 := by linear_combination -2*he
  constructor
  · intro hs
    have hh := (IsSquare.sq e).div hs
    have heq : e^2/(2+e)=2-e := by
      apply (div_eq_iff hp).mpr
      linear_combination -hprod
    rwa [heq] at hh
  · intro hs
    have hh := (IsSquare.sq e).div hs
    have heq : e^2/(2-e)=2+e := by
      apply (div_eq_iff hm).mpr
      linear_combination -hprod
    rwa [heq] at hh

theorem bitAtRoot_independent {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (e f : F) (he : e^2=2) (hf : f^2=2) : bitAtRoot e=bitAtRoot f := by
  classical
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (he.trans hf.symm)) with h | h
  · rw [h]
  · rw [h]
    have hh : IsSquare (2+-f) ↔ IsSquare (2+f) := by
      simpa only [sub_eq_add_neg] using (squareclass_root_sign h2 f hf).symm
    simp only [bitAtRoot,hh]

/-- The pole character bit. At primes appearing in P, Loc proves that the
chosen square root exists, and bitAtRoot_independent proves choice independence. -/
noncomputable def sigma (q : ℕ) : ZMod 2 := by
  classical
  exact if IsSquare (2+rootTwo q) then 0 else 1

theorem sigma_at_root (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (e : ZMod q) (he : e^2=2) : sigma q=bitAtRoot e := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 q).mp hh
    exact hq ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (Fact.out : q.Prime).ne_one)
  have hsq : IsSquare (2 : ZMod q) := ⟨e,by simpa only [pow_two] using he.symm⟩
  change bitAtRoot (rootTwo q)=bitAtRoot e
  exact bitAtRoot_independent h2 _ _ (rootTwo_sq q hsq) he

/-- Literal Legendre-character semantics of the F2 pole bit, for either root. -/
theorem sigma_character (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (e : ZMod q) (he : e^2=2) : quadraticChar (ZMod q) (2+e)=(-1 : ℤ)^(sigma q).val := by
  classical
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro hh
    have hd := (ZMod.natCast_eq_zero_iff 2 q).mp hh
    exact hq ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left (Fact.out : q.Prime).ne_one)
  have hn := two_add_root_ne_zero h2 e he
  rw [sigma_at_root q hq e he]
  by_cases hs : IsSquare (2+e) <;>
    norm_num [bitAtRoot,hs,quadraticChar_apply,quadraticCharFun,hn,ZMod.val_one_eq_one_mod]

noncomputable def P (p : ℚ) : ZMod 2 := by
  classical
  exact ∑ q ∈ (rationalSupport p).filter (fun q => q ≠ 2 ∧
    padicValRat q p < 0 ∧ Odd (padicValRat q p)), sigma q

/-- Exactly the p≡1 mod16 branch, interpreted in Z_2 as in the manuscript. -/
def UnitOne (p : ℚ) : Prop := ∃ u : ℤ_[2], (u : ℚ_[2])=(p : ℚ_[2]) ∧
  PadicInt.toZModPow 4 u=1

def UnitFifteen (p : ℚ) : Prop := ∃ u : ℤ_[2], (u : ℚ_[2])=(p : ℚ_[2]) ∧
  PadicInt.toZModPow 4 u=15

theorem unit_branches_disjoint (p : ℚ) : ¬ (UnitOne p ∧ UnitFifteen p) := by
  rintro ⟨⟨u,hu,hr⟩,⟨v,hv,hs⟩⟩
  have he : u=v := Subtype.ext (hu.trans hv.symm)
  rw [he,hs] at hr
  exact (by decide : (15 : ZMod 16) ≠ 1) hr

noncomputable def T (p : ℚ) : ZMod 2 := by
  classical
  exact if padicValRat 2 p ≠ 0 then B p+P p else
    if UnitOne p then (if padicValRat 2 (p-1)=5 then 1 else 0)+B p+P p else
      (if padicValRat 2 (p+1)=5 then 1 else 0)+A p+P p

theorem T_nonunit (p : ℚ) (hv : padicValRat 2 p ≠ 0) : T p=B p+P p := by
  simp only [T,if_pos hv]

theorem T_unit_one (p : ℚ) (hv : padicValRat 2 p=0) (h : UnitOne p) :
    T p=(if padicValRat 2 (p-1)=5 then 1 else 0)+B p+P p := by
  simp only [T,hv,ne_eq,not_true_eq_false,if_false,if_pos h]

theorem T_unit_fifteen (p : ℚ) (hv : padicValRat 2 p=0) (h : UnitFifteen p) :
    T p=(if padicValRat 2 (p+1)=5 then 1 else 0)+A p+P p := by
  have hn : ¬ UnitOne p := fun hh => unit_branches_disjoint p ⟨hh,h⟩
  simp only [T,hv,ne_eq,not_true_eq_false,if_false,hn]

/-- Loc leaves exactly the branches used in the displayed piecewise T.
Thus the default case in its total definition inserts no extra arithmetic branch. -/
theorem exact_T_branches (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p) :
    padicValRat 2 p ≠ 0 ∨
      (padicValRat 2 p=0 ∧ UnitOne p) ∨ (padicValRat 2 p=0 ∧ UnitFifteen p) := by
  by_cases hv : padicValRat 2 p ≠ 0
  · exact Or.inl hv
  have hv0 : padicValRat 2 p=0 := not_ne_iff.mp hv
  have hvp : (p : ℚ_[2]).valuation=0 := by rwa [Padic.valuation_ratCast]
  rcases HasseNorms.dyadic_conclusion p hp hL with h | h | h | h
  · rw [hvp] at h
    omega
  · rw [hvp] at h
    omega
  · obtain ⟨u,hu,hr,_⟩ := h
    exact Or.inr (Or.inl ⟨hv0,u,hu,hr⟩)
  · obtain ⟨u,hu,hr,_⟩ := h
    exact Or.inr (Or.inr ⟨hv0,u,hu,hr⟩)

/-- Every odd pole of odd depth in P is split for 2; no square-root existence
is added as an extra hypothesis to the obstruction definition. -/
theorem pole_root_exists (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (hodd : Odd (padicValRat q p)) :
    IsSquare (2 : ZMod q) := by
  by_contra hns
  have he := (HasseNorms.local_inert_parities p hp hL q hq
    (SqrtTwoGlobalNorm.nonsquare_two_completion hns)).1
  exact (Int.not_even_iff_odd.mpr hodd) he

/-- The displayed halves in A,B are honest integral halves on Loc. -/
theorem half_valuations_integral (p : ℚ) (hp : 1<p) (hL : HasseNorms.Loc p)
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (hns : ¬ IsSquare (2 : ZMod q)) :
    2*(padicValRat q (p-1)/2)=padicValRat q (p-1) ∧
    2*(padicValRat q (p+1)/2)=padicValRat q (p+1) := by
  obtain ⟨_,ha,hb⟩ := HasseNorms.local_inert_parities p hp hL q hq
    (SqrtTwoGlobalNorm.nonsquare_two_completion hns)
  exact ⟨Int.mul_ediv_cancel' (even_iff_two_dvd.mp ha),
    Int.mul_ediv_cancel' (even_iff_two_dvd.mp hb)⟩

#print axioms valuation_zero_outside_support
#print axioms mem_support_of_valuation_ne_zero
#print axioms rootTwo_sq
#print axioms squareclass_root_sign
#print axioms bitAtRoot_independent
#print axioms sigma_at_root
#print axioms sigma_character
#print axioms exact_T_branches
#print axioms pole_root_exists
#print axioms half_valuations_integral

end FourCorner.HasseObstructionArithmetic
