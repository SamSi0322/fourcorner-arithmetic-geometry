import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Ring.Parity

namespace FourCorner

private theorem squarefree_decomposition_exists (d : ℕ) :
    ∃ m : ℕ, Squarefree m ∧ ∃ t : ℕ, d = m * t ^ 2 := by
  obtain ⟨m, t, h, hm⟩ := Nat.sq_mul_squarefree d
  exact ⟨m, hm, t, by simpa [mul_comm] using h.symm⟩

/-- The squarefree kernel of a natural number, with value `1` at zero.
For positive inputs, uniqueness below makes the choice independent of its witness. -/
noncomputable def squarefreePart (d : ℕ) : ℕ :=
  if d = 0 then 1 else Classical.choose (squarefree_decomposition_exists d)

@[simp] theorem squarefreePart_zero : squarefreePart 0 = 1 := by
  simp [squarefreePart]

theorem squarefreePart_squarefree (d : ℕ) : Squarefree (squarefreePart d) := by
  by_cases hd : d = 0
  · simp [hd]
  · simpa [squarefreePart, hd] using
      (Classical.choose_spec (squarefree_decomposition_exists d)).1

theorem squarefreePart_decomposition (d : ℕ) :
    ∃ t : ℕ, d = squarefreePart d * t ^ 2 := by
  by_cases hd : d = 0
  · exact ⟨0, by simp [hd]⟩
  · simpa [squarefreePart, hd] using
      (Classical.choose_spec (squarefree_decomposition_exists d)).2

theorem squarefreePart_pos (d : ℕ) : 0 < squarefreePart d :=
  Nat.pos_of_ne_zero (squarefreePart_squarefree d).ne_zero

theorem squarefreePart_dvd (d : ℕ) : squarefreePart d ∣ d := by
  obtain ⟨t, ht⟩ := squarefreePart_decomposition d
  exact ⟨t ^ 2, ht⟩

theorem squarefreePart_decomposition_pos {d : ℕ} (hd : 0 < d) :
    ∃ t : ℕ, 0 < t ∧ d = squarefreePart d * t ^ 2 := by
  obtain ⟨t, ht⟩ := squarefreePart_decomposition d
  refine ⟨t, ?_, ht⟩
  by_contra h
  have hz : t = 0 := by omega
  simp [hz] at ht
  omega

theorem squarefreePart_odd {d : ℕ} (hd : Odd d) : Odd (squarefreePart d) := by
  obtain ⟨t, ht⟩ := squarefreePart_decomposition d
  rw [ht] at hd
  exact Nat.Odd.of_mul_left hd

theorem squarefreePart_coprime_left {d n : ℕ} (h : d.Coprime n) :
    (squarefreePart d).Coprime n :=
  h.of_dvd_left (squarefreePart_dvd d)

theorem squarefreePart_coprime_right {d n : ℕ} (h : d.Coprime n) :
    d.Coprime (squarefreePart n) :=
  h.of_dvd_right (squarefreePart_dvd n)

theorem squarefreePart_coprime {d n : ℕ} (h : d.Coprime n) :
    (squarefreePart d).Coprime (squarefreePart n) :=
  h.of_dvd (squarefreePart_dvd d) (squarefreePart_dvd n)

theorem squarefree_eq_of_mul_sq_eq {m n a b : ℕ}
    (hm : Squarefree m) (hn : Squarefree n) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : m * a ^ 2 = n * b ^ 2) : m = n := by
  apply Nat.eq_of_factorization_eq hm.ne_zero hn.ne_zero
  intro p
  have hf := congrArg (fun k : ℕ => k.factorization p) h
  simp only [Nat.factorization_mul hm.ne_zero (pow_ne_zero _ ha),
    Nat.factorization_mul hn.ne_zero (pow_ne_zero _ hb), Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hf
  have hm' := hm.natFactorization_le_one p
  have hn' := hn.natFactorization_le_one p
  omega

/-- A positive natural number has a unique squarefree factor after removing a square. -/
theorem squarefreePart_eq_of_decomposition {d m t : ℕ}
    (hd : 0 < d) (hm : Squarefree m) (h : d = m * t ^ 2) :
    squarefreePart d = m := by
  obtain ⟨s, hs, hds⟩ := squarefreePart_decomposition_pos hd
  have ht : t ≠ 0 := by
    intro ht
    simp [ht] at h
    omega
  exact squarefree_eq_of_mul_sq_eq (squarefreePart_squarefree d) hm
    (Nat.ne_of_gt hs) ht (hds.symm.trans h)

@[simp] theorem squarefreePart_of_squarefree {d : ℕ} (hd : Squarefree d) :
    squarefreePart d = d := by
  apply squarefreePart_eq_of_decomposition (Nat.pos_of_ne_zero hd.ne_zero) hd (t := 1)
  simp

/-- The canonical kernel keeps precisely the odd prime exponents. -/
theorem squarefreePart_factorization {d : ℕ} (hd : 0 < d) (p : ℕ) :
    (squarefreePart d).factorization p = d.factorization p % 2 := by
  obtain ⟨t, ht, hdt⟩ := squarefreePart_decomposition_pos hd
  have hfac := congrArg (fun k : ℕ => k.factorization p) hdt
  simp only [Nat.factorization_mul (squarefreePart_squarefree d).ne_zero
      (pow_ne_zero _ (Nat.ne_of_gt ht)), Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hfac
  have hb := (squarefreePart_squarefree d).natFactorization_le_one p
  omega

theorem squarefreePart_positive_odd_decomposition {d : ℕ} (hd : 0 < d) (ho : Odd d) :
    0 < squarefreePart d ∧ Odd (squarefreePart d) ∧ Squarefree (squarefreePart d) ∧
      ∃ t : ℕ, 0 < t ∧ d = squarefreePart d * t ^ 2 :=
  ⟨squarefreePart_pos d, squarefreePart_odd ho, squarefreePart_squarefree d,
    squarefreePart_decomposition_pos hd⟩

end FourCorner
