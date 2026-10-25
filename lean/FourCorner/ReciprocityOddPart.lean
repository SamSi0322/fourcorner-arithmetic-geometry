import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import FourCorner.ReciprocityPrimeProduct

set_option autoImplicit false
namespace FourCorner

/-- The parity exponent of the character modulo four. -/
def e4 (n : ℕ) : ℕ := if n % 4 = 3 then 1 else 0

/-- The odd part, with every factor of two removed. -/
def oddPart (n : ℕ) : ℕ := ordCompl[2] n

/-- The quadratic character modulo four of the odd part. -/
def oddPartChar (n : ℕ) : ℤ := jacobiSym (-1) (oddPart n)

lemma oddPart_odd {n : ℕ} (hn : 0 < n) : Odd (oddPart n) := by
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    (Nat.not_dvd_ordCompl Nat.prime_two hn.ne'))

lemma oddPart_dvd (n : ℕ) : oddPart n ∣ n := Nat.ordCompl_dvd n 2

lemma oddPart_eq_self {n : ℕ} (hn : Odd n) : oddPart n = n := by
  apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd n Nat.prime_two).mpr
  exact Or.inr (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hn))

lemma chi4_eq_neg_one_pow_e4 {n : ℕ} (hn : Odd n) :
    ZMod.χ₄ n = (-1 : ℤ) ^ e4 n := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h | h
  · simp [ZMod.χ₄_nat_one_mod_four h, e4, h]
  · simp [ZMod.χ₄_nat_three_mod_four h, e4, h]

lemma oddPartChar_sq {V : ℕ} (_hV : 0 < V) : oddPartChar V ^ 2 = 1 := by
  exact jacobiSym.sq_one (by simp)

lemma oddPartChar_of_odd {V : ℕ} (hV : Odd V) :
    oddPartChar V = (-1 : ℤ) ^ e4 V := by
  rw [oddPartChar, oddPart_eq_self hV, jacobiSym.at_neg_one hV,
    chi4_eq_neg_one_pow_e4 hV]

lemma jacobiSym_two_eq_one {s : ℕ} (hs : Odd s)
    (hs8 : s % 8 = 1 ∨ s % 8 = 7) : jacobiSym 2 s = 1 := by
  rw [jacobiSym.at_two hs, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [Nat.odd_iff.mp hs, hs8]

lemma jacobiSym_oddPart {s V : ℕ} (hs : Odd s)
    (hs8 : s % 8 = 1 ∨ s % 8 = 7) :
    jacobiSym (V : ℤ) s = jacobiSym (oddPart V : ℤ) s := by
  have hV : V = 2 ^ V.factorization 2 * oddPart V :=
    (Nat.ordProj_mul_ordCompl_eq_self V 2).symm
  conv_lhs => rw [hV]
  rw [Nat.cast_mul, jacobiSym.mul_left, Nat.cast_pow, Nat.cast_ofNat,
    jacobiSym.pow_left, jacobiSym_two_eq_one hs hs8, one_pow, one_mul]

lemma jacobiSym_odd_of_neg_eq_one {s d : ℕ} (hs : Odd s) (hd : Odd d)
    (hneg : jacobiSym (-(s : ℤ)) d = 1) :
    jacobiSym (d : ℤ) s = jacobiSym (-1) d ^ (1 + e4 s) := by
  have hc2 : jacobiSym (-1) d ^ 2 = 1 := jacobiSym.sq_one (by simp)
  have hc : jacobiSym (-1) d * jacobiSym (s : ℤ) d = 1 := by
    rw [← jacobiSym.mul_left, neg_one_mul]
    exact hneg
  have hsd : jacobiSym (s : ℤ) d = jacobiSym (-1) d := by
    calc
      jacobiSym (s : ℤ) d = jacobiSym (-1) d ^ 2 * jacobiSym (s : ℤ) d := by
        rw [hc2, one_mul]
      _ = jacobiSym (-1) d * (jacobiSym (-1) d * jacobiSym (s : ℤ) d) := by ring
      _ = jacobiSym (-1) d := by rw [hc, mul_one]
  rw [jacobiSym.quadratic_reciprocity' hd hs, qrSign,
    chi4_eq_neg_one_pow_e4 hs, jacobiSym.pow_left, hsd]
  rw [pow_add, pow_one, mul_comm]

/-- Primewise support controls the Jacobi symbol of a positive integer, after
removing every factor of two and applying quadratic reciprocity. -/
theorem jacobiSym_of_odd_prime_support {s V : ℕ} (hs : Odd s) (hV : 0 < V)
    (hs8 : s % 8 = 1 ∨ s % 8 = 7)
    (support : ∀ p : ℕ, p.Prime → Odd p → p ∣ V →
      jacobiSym (-(s : ℤ)) p = 1) :
    jacobiSym (V : ℤ) s = oddPartChar V ^ (1 + e4 s) := by
  rw [jacobiSym_oddPart hs hs8]
  apply jacobiSym_odd_of_neg_eq_one hs (oddPart_odd hV)
  apply jacobiSym_eq_one_of_prime_support
  intro p hp hpd
  exact support p hp ((oddPart_odd hV).of_dvd_nat hpd)
    (hpd.trans (oddPart_dvd V))

end FourCorner
