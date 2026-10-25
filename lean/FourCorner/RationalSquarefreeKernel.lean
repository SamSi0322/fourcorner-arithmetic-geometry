import FourCorner.RationalSquarefree

namespace FourCorner

/-- The canonical natural representative of the square class of a rational,
obtained by retaining the odd prime exponents in numerator times denominator. -/
noncomputable def rationalSquarefreePart (s : ℚ) : ℕ :=
  squarefreePart (s.num.natAbs * s.den)

theorem rationalSquarefreePart_pos (s : ℚ) : 0 < rationalSquarefreePart s :=
  squarefreePart_pos _

theorem rationalSquarefreePart_squarefree (s : ℚ) :
    Squarefree (rationalSquarefreePart s) := squarefreePart_squarefree _

/-- Removing the canonical squarefree part leaves a positive rational square. -/
theorem rationalSquarefreePart_decomposition {s : ℚ} (hs : 0 < s) :
    ∃ q : ℚ, 0 < q ∧ s = (rationalSquarefreePart s : ℚ) * q ^ 2 := by
  have hn : 0 < s.num := Rat.num_pos.mpr hs
  have habs : (s.num.natAbs : ℤ) = s.num := Int.natAbs_of_nonneg hn.le
  have ha : 0 < s.num.natAbs := by
    exact_mod_cast (show (0 : ℤ) < (s.num.natAbs : ℤ) by rwa [habs])
  have hcast : (s.num.natAbs : ℚ) = (s.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) habs
  have hsrep : s = (s.num.natAbs : ℚ) / s.den := by
    rw [hcast, Rat.num_div_den]
  obtain ⟨t, ht, heq⟩ := squarefreePart_decomposition_pos (Nat.mul_pos ha s.den_pos)
  refine ⟨(t : ℚ) / s.den, div_pos (by exact_mod_cast ht)
    (by exact_mod_cast s.den_pos), ?_⟩
  have hd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have heqq : (s.num.natAbs : ℚ) * s.den =
      (rationalSquarefreePart s : ℚ) * (t : ℚ) ^ 2 := by exact_mod_cast heq
  conv_lhs => rw [hsrep]
  field_simp
  nlinarith [heqq]

/-- Any positive squarefree natural representative of a positive rational
square class is its canonical rational squarefree part. -/
theorem rationalSquarefreePart_eq_of_decomposition {s : ℚ} {n : ℕ} {w : ℚ}
    (hs : 0 < s) (hn : Squarefree n) (hw : 0 < w)
    (heq : s = (n : ℚ) * w ^ 2) : rationalSquarefreePart s = n := by
  obtain ⟨q, hq, hcanon⟩ := rationalSquarefreePart_decomposition hs
  exact squarefree_eq_of_rat_mul_sq_eq (rationalSquarefreePart_squarefree s) hn
    hq hw (hcanon.symm.trans heq)

end FourCorner

#print axioms FourCorner.rationalSquarefreePart_decomposition
#print axioms FourCorner.rationalSquarefreePart_eq_of_decomposition
