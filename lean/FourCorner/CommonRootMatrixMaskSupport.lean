import Mathlib.Data.Nat.Squarefree

namespace FourCorner

open scoped BigOperators

/-- A squarefree even natural number supported on `2` and a list of distinct
odd primes is the product of `2` and exactly those listed primes that divide it. -/
theorem squarefree_even_eq_two_mul_prod_dvd {r n : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hne : ∀ i, p i ≠ 2) (hn : Squarefree n) (h2 : 2 ∣ n)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ n → q = 2 ∨ ∃ i, q = p i) :
    n = 2 * ∏ i ∈ Finset.univ.filter (fun i => p i ∣ n), p i := by
  classical
  let s : Finset (Fin r) := Finset.univ.filter (fun i => p i ∣ n)
  have hset : n.primeFactors = insert 2 (s.image p) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
      rcases hsupport q hqprime hqdvd with rfl | ⟨i, rfl⟩
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨i, by simpa [s] using hqdvd, rfl⟩)
    · intro hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact Nat.prime_two.mem_primeFactors h2 hn.ne_zero
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        exact (hp i).mem_primeFactors (by simpa [s] using hi) hn.ne_zero
  have hnot : 2 ∉ s.image p := by
    rintro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact hne i hi
  calc
    n = ∏ q ∈ n.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hn).symm
    _ = 2 * ∏ q ∈ s.image p, q := by rw [hset, Finset.prod_insert hnot]
    _ = 2 * ∏ i ∈ s, p i := by rw [Finset.prod_image hinj.injOn]

end FourCorner
