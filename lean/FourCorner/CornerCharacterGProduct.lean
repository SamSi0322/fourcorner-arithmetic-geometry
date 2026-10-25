import FourCorner.ReciprocityOddPart

set_option autoImplicit false
namespace FourCorner

/-- The manuscript's literal character product, with each prime carrying its
full valuation in `n`. -/
def literalG (n : ℕ) : ℤ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p % 4 = 3), (-1 : ℤ) ^ n.factorization p

private lemma jacobiSym_prod (a : ℤ) (S : Finset ℕ) (f : ℕ → ℕ)
    (hS : ∀ p ∈ S, f p ≠ 0) :
    jacobiSym a (∏ p ∈ S, f p) = ∏ p ∈ S, jacobiSym a (f p) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      jacobiSym.mul_right' a (hS p (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun q hq => hS q (Finset.mem_insert_of_mem hq))),
      ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))]

lemma jacobiSym_neg_one_two : jacobiSym (-1) 2 = 1 := by
  rw [jacobiSym.mod_left]
  norm_num

lemma jacobiSym_neg_one_prime {p : ℕ} (hp : p.Prime) :
    jacobiSym (-1) p = if p % 4 = 3 then -1 else 1 := by
  rcases hp.eq_two_or_odd' with rfl | ho
  · norm_num [jacobiSym_neg_one_two]
  · rw [jacobiSym.at_neg_one ho]
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ho) with h | h
    · simp [h, ZMod.χ₄_nat_one_mod_four h]
    · simp [h, ZMod.χ₄_nat_three_mod_four h]

/-- The factorization expansion retains the multiplicity of every prime. -/
lemma jacobiSym_factorization_product (a : ℤ) {n : ℕ} (hn : 0 < n) :
    jacobiSym a n = ∏ p ∈ n.primeFactors, jacobiSym a p ^ n.factorization p := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn.ne']
  rw [jacobiSym_prod a _ _ (fun p hp =>
    pow_ne_zero _ (Nat.mem_primeFactors.mp hp).1.ne_zero)]
  simp_rw [jacobiSym.pow_right]

lemma literalG_eq_jacobiSym {n : ℕ} (hn : 0 < n) :
    literalG n = jacobiSym (-1) n := by
  rw [literalG, Finset.prod_filter, jacobiSym_factorization_product (-1) hn]
  apply Finset.prod_congr rfl
  intro p hp
  rw [jacobiSym_neg_one_prime (Nat.mem_primeFactors.mp hp).1]
  split_ifs <;> simp

lemma jacobiSym_neg_one_eq_oddPartChar {n : ℕ} (hn : 0 < n) :
    jacobiSym (-1) n = oddPartChar n := by
  have heq : n = 2 ^ n.factorization 2 * oddPart n :=
    (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have ho : oddPart n ≠ 0 := by
    have hh := Nat.odd_iff.mp (oddPart_odd hn)
    omega
  conv_lhs => rw [heq]
  rw [jacobiSym.mul_right' (-1) (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) ho,
    jacobiSym.pow_right, jacobiSym_neg_one_two, one_pow, one_mul]
  rfl

/-- The literal prime-valuation product in the manuscript is exactly the
quadratic character of the odd part used in the reciprocity proof. -/
theorem literalG_eq_oddPartChar {n : ℕ} (hn : 0 < n) :
    literalG n = oddPartChar n :=
  (literalG_eq_jacobiSym hn).trans (jacobiSym_neg_one_eq_oddPartChar hn)

/-- The same literal product, written with the standard natural valuation. -/
def paperG (n : ℕ) : ℤ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p % 4 = 3), (-1 : ℤ) ^ padicValNat p n

lemma paperG_eq_literalG (n : ℕ) : paperG n = literalG n := by
  unfold paperG literalG
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_def n (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1]

/-- The manuscript's valuation-product definition equals the odd-part
character, including even positive arguments and arbitrary prime powers. -/
theorem paperG_eq_oddPartChar {n : ℕ} (hn : 0 < n) :
    paperG n = oddPartChar n :=
  (paperG_eq_literalG n).trans (literalG_eq_oddPartChar hn)

end FourCorner

#print axioms FourCorner.literalG_eq_oddPartChar

#print axioms FourCorner.paperG_eq_oddPartChar
