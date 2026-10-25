import FourCorner.RationalSquarefree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! Rational square classes with controlled odd-prime support. The valuations
here are integer-valued, so primes in rational denominators are included. -/

namespace FourCorner

/-- A prime dividing the squarefree part occurs to odd order in the rational
number, including when the square factor contributes a negative valuation. -/
theorem squarefree_rat_mul_sq_prime_odd {n p : ℕ} {q u : ℚ}
    (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n)
    (hu : u ≠ 0) (hq : q = (n : ℚ) * u ^ 2) :
    Odd (padicValRat p q) := by
  let : Fact p.Prime := ⟨hp⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne_zero
  have hv : padicValNat p n = 1 := by
    rw [← Nat.factorization_def n hp]
    exact Nat.factorization_eq_one_of_squarefree hn hp hpn
  rw [hq, padicValRat.mul hnq (pow_ne_zero 2 hu), padicValRat.of_nat,
    hv, padicValRat.pow]
  refine ⟨padicValRat p u, ?_⟩
  push_cast
  ring

/-- Every positive rational with constrained odd valuation support is a
positive squarefree natural, supported at the permitted primes and `2`,
times a positive rational square. -/
theorem positive_rat_squarefree_support_decomposition {P : ℕ → Prop} {q : ℚ}
    (hq : 0 < q)
    (hsupport : ∀ p : ℕ, p.Prime → p ≠ 2 → Odd (padicValRat p q) → P p) :
    ∃ n : ℕ, 0 < n ∧ Squarefree n ∧
      (∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ P p) ∧
      ∃ u : ℚ, 0 < u ∧ q = (n : ℚ) * u ^ 2 := by
  obtain ⟨n, hn, hns, u, hu, hqu⟩ := positive_rat_squarefree_decomposition hq
  refine ⟨n, hn, hns, ?_, u, hu, hqu⟩
  intro p hp hpn
  by_cases hp2 : p = 2
  · exact Or.inl hp2
  · exact Or.inr (hsupport p hp hp2
      (squarefree_rat_mul_sq_prime_odd hns hp hpn (ne_of_gt hu) hqu))

/-- Absolute value does not change any rational prime valuation. -/
theorem padicValRat_abs_eq (p : ℕ) (q : ℚ) :
    padicValRat p |q| = padicValRat p q := by
  rcases le_total 0 q with hq | hq
  · rw [abs_of_nonneg hq]
  · rw [abs_of_nonpos hq, padicValRat.neg]

/-- Every nonzero rational with constrained odd valuation support is a sign,
a positive squarefree natural supported at the permitted primes and `2`,
and a nonzero rational square. The square factor is chosen positive. -/
theorem rat_squarefree_support_decomposition {P : ℕ → Prop} {q : ℚ}
    (hq : q ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ≠ 2 → Odd (padicValRat p q) → P p) :
    ∃ n : ℕ, 0 < n ∧ Squarefree n ∧
      (∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ P p) ∧
      ∃ ε u : ℚ, (ε = 1 ∨ ε = -1) ∧ 0 < u ∧
        q = ε * (n : ℚ) * u ^ 2 := by
  have ha : ∀ p : ℕ, p.Prime → p ≠ 2 → Odd (padicValRat p |q|) → P p := by
    intro p hp hp2 hv
    rw [padicValRat_abs_eq] at hv
    exact hsupport p hp hp2 hv
  obtain ⟨n, hn, hns, hnP, u, hu, hqu⟩ :=
    positive_rat_squarefree_support_decomposition (abs_pos.mpr hq) ha
  refine ⟨n, hn, hns, hnP, ?_⟩
  rcases le_total 0 q with hqpos | hqneg
  · refine ⟨1, u, Or.inl rfl, hu, ?_⟩
    simpa only [one_mul, abs_of_nonneg hqpos] using hqu
  · refine ⟨-1, u, Or.inr rfl, hu, ?_⟩
    rw [abs_of_nonpos hqneg] at hqu
    simpa only [neg_neg, neg_mul, one_mul] using congrArg (fun x : ℚ => -x) hqu

/-- An explicit finite product of permitted primes represents the square
class; no abstract subgroup or additional generation assumption is needed. -/
theorem rat_prime_product_support_decomposition {P : ℕ → Prop} {q : ℚ}
    (hq : q ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ≠ 2 → Odd (padicValRat p q) → P p) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p = 2 ∨ P p)) ∧
      ∃ ε u : ℚ, (ε = 1 ∨ ε = -1) ∧ 0 < u ∧
        q = ε * (∏ p ∈ S, (p : ℚ)) * u ^ 2 := by
  obtain ⟨n, _, hns, hnP, ε, u, hε, hu, hqu⟩ :=
    rat_squarefree_support_decomposition hq hsupport
  refine ⟨n.primeFactors, ?_, ε, u, hε, hu, ?_⟩
  · intro p hp
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hprime, hnP p hprime hdvd⟩
  · have hprod : (∏ p ∈ n.primeFactors, (p : ℚ)) = (n : ℚ) := by
      simpa only [Nat.cast_prod] using
        congrArg (fun a : ℕ => (a : ℚ)) (Nat.prod_primeFactors_of_squarefree hns)
    rw [hprod]
    exact hqu

end FourCorner

#print axioms FourCorner.squarefree_rat_mul_sq_prime_odd
#print axioms FourCorner.positive_rat_squarefree_support_decomposition
#print axioms FourCorner.rat_squarefree_support_decomposition
#print axioms FourCorner.rat_prime_product_support_decomposition
