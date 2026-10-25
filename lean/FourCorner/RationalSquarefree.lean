import FourCorner.SquarefreePart
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Existence and uniqueness of a positive squarefree normalization of a
positive rational number. -/

namespace FourCorner

/-- A positive rational number is a ratio of positive natural numbers. -/
theorem positive_rat_nat_fraction {t : ℚ} (ht : 0 < t) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ t = (a : ℚ) / b := by
  have hn : 0 < t.num := Rat.num_pos.mpr ht
  have habs : (t.num.natAbs : ℤ) = t.num := Int.natAbs_of_nonneg hn.le
  refine ⟨t.num.natAbs, t.den, ?_, t.den_pos, ?_⟩
  · exact_mod_cast (show (0 : ℤ) < (t.num.natAbs : ℤ) by rwa [habs])
  · have hcast : (t.num.natAbs : ℚ) = (t.num : ℚ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) habs
    rw [hcast, Rat.num_div_den]

/-- Every positive rational is a positive squarefree natural times a positive
rational square. -/
theorem positive_rat_squarefree_decomposition {t : ℚ} (ht : 0 < t) :
    ∃ n : ℕ, 0 < n ∧ Squarefree n ∧ ∃ q : ℚ, 0 < q ∧ t = (n : ℚ) * q ^ 2 := by
  obtain ⟨a, b, ha, hb, ht⟩ := positive_rat_nat_fraction ht
  obtain ⟨s, hs, hdecomp⟩ := squarefreePart_decomposition_pos (Nat.mul_pos ha hb)
  refine ⟨squarefreePart (a * b), squarefreePart_pos _, squarefreePart_squarefree _,
    (s : ℚ) / b, div_pos (by exact_mod_cast hs) (by exact_mod_cast hb), ?_⟩
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hrat : (a : ℚ) * b = (squarefreePart (a * b) : ℚ) * (s : ℚ) ^ 2 := by
    exact_mod_cast hdecomp
  rw [ht]
  field_simp
  nlinarith

/-- Once the positive natural factor is fixed, its positive rational square
factor is unique. -/
theorem positive_rat_square_factor_unique {n : ℕ} (hn : 0 < n)
    {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : (n : ℚ) * q ^ 2 = (n : ℚ) * r ^ 2) : q = r := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : q ^ 2 = r ^ 2 := mul_left_cancel₀ hnq h
  nlinarith

/-- Squarefree natural factors in positive rational square decompositions are
equal. Clearing the rational denominators reduces this to natural uniqueness. -/
theorem squarefree_eq_of_rat_mul_sq_eq {m n : ℕ} {q r : ℚ}
    (hm : Squarefree m) (hn : Squarefree n) (hq : 0 < q) (hr : 0 < r)
    (h : (m : ℚ) * q ^ 2 = (n : ℚ) * r ^ 2) : m = n := by
  obtain ⟨a, b, ha, hb, hq⟩ := positive_rat_nat_fraction hq
  obtain ⟨c, d, hc, hd, hr⟩ := positive_rat_nat_fraction hr
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hq, hr] at h
  field_simp at h
  apply squarefree_eq_of_mul_sq_eq hm hn (mul_ne_zero ha.ne' hd.ne')
    (mul_ne_zero hc.ne' hb.ne')
  have hh : (m : ℚ) * ((a : ℚ) * d) ^ 2 = (n : ℚ) * ((c : ℚ) * b) ^ 2 := by
    nlinarith [h]
  exact_mod_cast hh

/-- Both the squarefree natural factor and its positive rational scale are
unique. -/
theorem positive_rat_squarefree_decomposition_unique {t : ℚ} {m n : ℕ} {q r : ℚ}
    (hm : Squarefree m) (hn : Squarefree n) (hq : 0 < q) (hr : 0 < r)
    (hmq : t = (m : ℚ) * q ^ 2) (hnr : t = (n : ℚ) * r ^ 2) :
    m = n ∧ q = r := by
  have heq := hmq.symm.trans hnr
  have hmn := squarefree_eq_of_rat_mul_sq_eq hm hn hq hr heq
  refine ⟨hmn, ?_⟩
  subst n
  exact positive_rat_square_factor_unique (Nat.pos_of_ne_zero hm.ne_zero) hq hr heq

/-- A positive rational has exactly one positive squarefree natural factor
after removing a positive rational square. -/
theorem positive_rat_exists_unique_squarefree {t : ℚ} (ht : 0 < t) :
    ∃! n : ℕ, 0 < n ∧ Squarefree n ∧ ∃ q : ℚ, 0 < q ∧ t = (n : ℚ) * q ^ 2 := by
  obtain ⟨n, hn, hns, q, hq, hnt⟩ := positive_rat_squarefree_decomposition ht
  refine ⟨n, ⟨hn, hns, q, hq, hnt⟩, ?_⟩
  rintro m ⟨_, hms, r, hr, hmt⟩
  exact squarefree_eq_of_rat_mul_sq_eq hms hns hr hq (hmt.symm.trans hnt)

/-- The full normalization, including its positive scale, is uniquely
determined by a positive rational number. -/
theorem positive_rat_exists_unique_squarefree_pair {t : ℚ} (ht : 0 < t) :
    ∃! p : ℕ × ℚ,
      0 < p.1 ∧ Squarefree p.1 ∧ 0 < p.2 ∧ t = (p.1 : ℚ) * p.2 ^ 2 := by
  obtain ⟨n, hn, hns, q, hq, hnt⟩ := positive_rat_squarefree_decomposition ht
  refine ⟨(n, q), ⟨hn, hns, hq, hnt⟩, ?_⟩
  rintro ⟨m, r⟩ ⟨_, hms, hr, hmt⟩
  obtain ⟨hmn, hrq⟩ := positive_rat_squarefree_decomposition_unique hms hns hr hq hmt hnt
  exact Prod.ext hmn hrq

end FourCorner

#print axioms FourCorner.positive_rat_nat_fraction
#print axioms FourCorner.positive_rat_squarefree_decomposition
#print axioms FourCorner.positive_rat_square_factor_unique
#print axioms FourCorner.squarefree_eq_of_rat_mul_sq_eq
#print axioms FourCorner.positive_rat_squarefree_decomposition_unique
#print axioms FourCorner.positive_rat_exists_unique_squarefree
#print axioms FourCorner.positive_rat_exists_unique_squarefree_pair
