import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace FourCorner

/-- Prime support suffices for a Jacobi symbol to be one. The product defining
the symbol includes every prime factor with its full multiplicity. -/
theorem jacobiSym_eq_one_of_prime_support {a : ℤ} {b : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ b → jacobiSym a p = 1) :
    jacobiSym a b = 1 := by
  apply List.prod_eq_one
  intro z hz
  obtain ⟨p, hp, rfl⟩ := List.mem_pmap.mp hz
  let : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactorsList hp⟩
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact h p (Nat.prime_of_mem_primeFactorsList hp)
    (Nat.dvd_of_mem_primeFactorsList hp)

end FourCorner
