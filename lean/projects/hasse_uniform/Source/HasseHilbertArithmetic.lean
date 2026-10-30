import HasseObstructionArithmetic
import HilbertWellDefinedHigh11

/-! Usable arithmetic local signs on genuine nonzero rational coefficients.
The imported global product theorem is proved from quadratic reciprocity.
No reciprocity, local symbol or source-evaluation assertion is a hypothesis.
-/
namespace FourCorner.HasseHilbertArithmetic

open HilbertArithmeticHigh11 HilbertWellDefinedHigh11 HasseObstructionArithmetic

theorem rationalSign_symm (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (v : ℕ) :
    rationalSign a b ha hb v=rationalSign b a hb ha v :=
  presentationSign_symm _ _ _

theorem rationalSign_sq_one (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (v : ℕ) :
    (rationalSign a b ha hb v)^2=1 := by
  let xs := primePresentation a ha
  let ys := primePresentation b hb
  have hh := square_eval_sign (xs++xs) ys (evalPresentation xs)
    (HilbertOddFormulaHigh11.evalPresentation_ne_zero xs)
    (by rw [evalPresentation_append,pow_two]) v
  rw [presentationSign_append_left] at hh
  simpa only [rationalSign,xs,ys,pow_two] using hh

private theorem pow_even_eq_one {z : ℤ} {n : ℕ} (hz : z^2=1) (hn : Even n) : z^n=1 := by
  obtain ⟨k,hk⟩ := hn
  have he : n=2*k := by omega
  rw [he,pow_mul,hz,one_pow]

/-- The standard odd-prime formula vanishes when both actual valuations
are even. Negative valuations and arbitrary rational denominators are included. -/
theorem rationalSign_one_of_even_valuations (q : OddPrime) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : Even (padicValRat q.val a)) (hvb : Even (padicValRat q.val b)) :
    rationalSign a b ha hb q.val=1 := by
  let xs := primePresentation a ha
  let ys := primePresentation b hb
  have hax := HilbertOddFormulaHigh11.rational_presentation_valuation q xs
    (squareScale a ha) a (squareScale_spec a ha).1 (squareScale_spec a ha).2
  have hby := HilbertOddFormulaHigh11.rational_presentation_valuation q ys
    (squareScale b hb) b (squareScale_spec b hb).1 (squareScale_spec b hb).2
  have hx : Even (HilbertOddFormulaHigh11.order q xs) := by
    rw [Nat.even_iff]
    rw [Int.even_iff] at hva
    omega
  have hy : Even (HilbertOddFormulaHigh11.order q ys) := by
    rw [Nat.even_iff]
    rw [Int.even_iff] at hvb
    omega
  change presentationSign xs ys q.val=1
  rw [HilbertOddFormulaHigh11.presentation_odd_formula]
  simp only [HilbertOddFormulaHigh11.formula]
  rw [((hx.mul_right _).mul_right _).neg_one_pow,
    pow_even_eq_one (legendreSym.sq_one q.val
      (HilbertOddFormulaHigh11.unit_residue_nonzero q xs)) hy,
    pow_even_eq_one (legendreSym.sq_one q.val
      (HilbertOddFormulaHigh11.unit_residue_nonzero q ys)) hx]
  norm_num

private theorem presentation_negativeCount_parity (a : ℚ) (ha : a ≠ 0) :
    Even (negativeCount (primePresentation a ha)) ↔ 0<a := by
  let xs := primePresentation a ha
  let s := squareScale a ha
  have hs := (squareScale_spec a ha).1
  have he := (squareScale_spec a ha).2
  have hs2 : 0<s^2 := sq_pos_of_ne_zero hs
  constructor
  · intro hh
    have hp := signed_eval_positive xs
    rw [hh.neg_one_pow] at hp
    simp only [one_mul] at hp
    rw [he]
    exact mul_pos hp hs2
  · intro hp
    apply negativeCount_even_of_eval_positive
    rw [he] at hp
    exact (mul_pos_iff_of_pos_right hs2).mp hp

/-- The literal real Hilbert-sign formula for arbitrary nonzero rationals. -/
theorem rationalSign_real (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    rationalSign a b ha hb 0=if a<0 ∧ b<0 then -1 else 1 := by
  classical
  change presentationSign (primePresentation a ha) (primePresentation b hb) 0=_
  rw [presentation_real_formula]
  by_cases hpa : 0<a
  · have he := (presentation_negativeCount_parity a ha).mpr hpa
    rw [(he.mul_right _).neg_one_pow]
    simp [not_lt_of_ge (le_of_lt hpa)]
  by_cases hpb : 0<b
  · have he := (presentation_negativeCount_parity b hb).mpr hpb
    rw [(he.mul_left _).neg_one_pow]
    simp [not_lt_of_ge (le_of_lt hpb)]
  have hna : a<0 := lt_of_le_of_ne (le_of_not_gt hpa) ha
  have hnb : b<0 := lt_of_le_of_ne (le_of_not_gt hpb) hb
  have hoa : Odd (negativeCount (primePresentation a ha)) := by
    apply Nat.not_even_iff_odd.mp
    rw [presentation_negativeCount_parity]
    exact hpa
  have hob : Odd (negativeCount (primePresentation b hb)) := by
    apply Nat.not_even_iff_odd.mp
    rw [presentation_negativeCount_parity]
    exact hpb
  rw [(hoa.mul hob).neg_one_pow]
  simp [hna,hnb]

/-- The explicit sign has no unsupported composite places. -/
theorem rationalSign_one_of_not_prime (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : ℕ) (hv0 : v ≠ 0) (hv2 : v ≠ 2) (hv : ¬ v.Prime) :
    rationalSign a b ha hb v=1 := by
  apply presentationSign_one_outside _ _ v hv0 hv2
  · exact fun hh => hv (listSupport_prime _ hh)
  · exact fun hh => hv (listSupport_prime _ hh)

/-- The actual numerator/denominator support, together with infinity and two,
contains every nontrivial arithmetic Hilbert sign. -/
theorem rationalSign_one_outside_rational_support (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0)
    (v : ℕ) (hv : v ∉ ({0,2} ∪ rationalSupport a ∪ rationalSupport b)) :
    rationalSign a b ha hb v=1 := by
  have hvs : v≠0 ∧ v≠2 ∧ v∉rationalSupport a ∧ v∉rationalSupport b := by
    simpa only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,not_or,and_assoc] using hv
  by_cases hp : v.Prime
  · apply rationalSign_one_of_even_valuations ⟨v,hp,hvs.2.1⟩ a b ha hb
    · rw [valuation_zero_outside_support a ha v hp hvs.2.2.1]
      exact ⟨0,by simp⟩
    · rw [valuation_zero_outside_support b hb v hp hvs.2.2.2]
      exact ⟨0,by simp⟩
  · exact rationalSign_one_of_not_prime a b ha hb v hvs.1 hvs.2.1 hp

/-- An exact finite Hilbert product over the original rational coefficient
support, rather than the support of an arbitrarily chosen prime presentation. -/
theorem rational_reciprocity_on_rational_support (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∏ v ∈ ({0,2} ∪ rationalSupport a ∪ rationalSupport b),rationalSign a b ha hb v)=1 := by
  obtain ⟨S,hS0,hS2,hprod,hout⟩ := rational_reciprocity a b ha hb
  let T := {0,2} ∪ rationalSupport a ∪ rationalSupport b
  have hleft : (∏ v ∈ S ∪ T,rationalSign a b ha hb v)=
      (∏ v ∈ S,rationalSign a b ha hb v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_left
    intro v hv hnv
    exact hout v hnv
  have hright : (∏ v ∈ S ∪ T,rationalSign a b ha hb v)=
      (∏ v ∈ T,rationalSign a b ha hb v) := by
    symm
    apply Finset.prod_subset Finset.subset_union_right
    intro v hv hnv
    exact rationalSign_one_outside_rational_support a b ha hb v hnv
  exact hright.symm.trans (hleft.trans hprod)

#print axioms rationalSign_symm
#print axioms rationalSign_sq_one
#print axioms rationalSign_one_of_even_valuations
#print axioms rationalSign_real
#print axioms rationalSign_one_outside_rational_support
#print axioms rational_reciprocity_on_rational_support

end FourCorner.HasseHilbertArithmetic
