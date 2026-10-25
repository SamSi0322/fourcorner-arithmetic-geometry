import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Squarefree
import FourCorner.ReciprocitySigma16
import FourCorner.SupportProductEight
import Mathlib.Tactic.Ring
import FourCorner.ReciprocityOddPart

set_option autoImplicit false
namespace FourCorner

lemma jacobiSym_finset_prod (a : ℤ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ≠ 0) :
    jacobiSym a (∏ p ∈ S, p) = ∏ p ∈ S, jacobiSym a p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      jacobiSym.mul_right' a (hS p (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun q hq => hS q (Finset.mem_insert_of_mem hq))),
      ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))]

lemma jacobiSym_squarefree_product (a : ℤ) {m : ℕ} (hm : Squarefree m) :
    jacobiSym a m = ∏ p ∈ m.primeFactors, jacobiSym a p := by
  nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hm]
  exact jacobiSym_finset_prod a _ (fun p hp => (Nat.mem_primeFactors.mp hp).1.ne_zero)

/-- Multiplying the local ramified identities over the squarefree colour. -/
lemma jacobiSym_ramified_product {m other V k : ℕ} (hm : Squarefree m)
    (hs : ∀ p : ℕ, p.Prime → p ∣ m → p % 8 = 1 ∨ p % 8 = 7)
    (hlocal : ∀ p : ℕ, p.Prime → p ∣ m →
      jacobiSym (V : ℤ) p = jacobiSym (other : ℤ) p * sigma16 p ^ k) :
    jacobiSym (V : ℤ) m = jacobiSym (other : ℤ) m * sigma16 m ^ k := by
  rw [jacobiSym_squarefree_product _ hm, jacobiSym_squarefree_product _ hm,
    sigma16_primeFactors_prod hm (fun p hp =>
      hs p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1),
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact hlocal p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1

lemma e4_mul_mod_two {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    e4 (a*b) = (e4 a + e4 b) % 2 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ha) with ha | ha <;>
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hb) with hb | hb <;>
    norm_num [e4, Nat.mul_mod, ha, hb]

/-- Ordinary Jacobi reciprocity with the sign expressed by residue parities. -/
lemma jacobiSym_reciprocity_product {a b : ℕ} (ha : Odd a) (hb : Odd b)
    (hc : a.Coprime b) :
    jacobiSym (b : ℤ) a * jacobiSym (a : ℤ) b = (-1 : ℤ)^(e4 a * e4 b) := by
  have hsq : jacobiSym (a : ℤ) b ^ 2 = 1 :=
    jacobiSym.sq_one (by simpa using hc)
  have hqr := jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp hb) (Nat.odd_iff.mp ha)
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ha) with ha | ha <;>
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hb) with hb | hb <;>
    simp only [ha, hb] at hqr
  all_goals
    norm_num at hqr
    rw [← hqr]
    simp only [e4, ha, hb]
    norm_num
    first | exact hsq | simpa [pow_two] using hsq

/-- The section-four master identity, obtained from the ramified prime products
and two applications of ordinary quadratic reciprocity. -/
theorem pair_reciprocity_master {mi mj V d : ℕ}
    (hi : Odd mi) (hj : Odd mj) (hfi : Squarefree mi) (hfj : Squarefree mj)
    (hcop : mi.Coprime mj) (hV : 0 < V)
    (hsi : ∀ p : ℕ, p.Prime → p ∣ mi → p % 8 = 1 ∨ p % 8 = 7)
    (hsj : ∀ p : ℕ, p.Prime → p ∣ mj → p % 8 = 1 ∨ p % 8 = 7)
    (support : ∀ p : ℕ, p.Prime → Odd p → p ∣ V →
      jacobiSym (-((mi*mj : ℕ) : ℤ)) p = 1)
    (rami : ∀ p : ℕ, p.Prime → p ∣ mi →
      jacobiSym (V : ℤ) p = jacobiSym (mj : ℤ) p * sigma16 p ^ (d-1))
    (ramj : ∀ p : ℕ, p.Prime → p ∣ mj →
      jacobiSym (V : ℤ) p = jacobiSym (mi : ℤ) p * sigma16 p ^ (d-1)) :
    oddPartChar V ^ (1 + e4 (mi*mj)) =
      (-1 : ℤ) ^ (e4 mi * e4 mj) * sigma16 (mi*mj) ^ (d-1) := by
  have hi8 := nat_mod_eight_of_prime_divisors mi hfi.ne_zero hsi
  have hj8 := nat_mod_eight_of_prime_divisors mj hfj.ne_zero hsj
  rw [← jacobiSym_of_odd_prime_support (hi.mul hj) hV
    (mod_eight_mul_of_one_or_seven hi8 hj8) support,
    jacobiSym.mul_right' _ hfi.ne_zero hfj.ne_zero,
    jacobiSym_ramified_product hfi hsi rami,
    jacobiSym_ramified_product hfj hsj ramj,
    sigma16_mul hi8 hj8, mul_pow]
  calc
    _ = (jacobiSym (mj : ℤ) mi * jacobiSym (mi : ℤ) mj) *
        (sigma16 mi ^ (d-1) * sigma16 mj ^ (d-1)) := by ring
    _ = _ := by rw [jacobiSym_reciprocity_product hi hj hcop]

end FourCorner

#print axioms FourCorner.pair_reciprocity_master
