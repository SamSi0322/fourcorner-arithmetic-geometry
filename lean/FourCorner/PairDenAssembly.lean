import FourCorner.PairRatDen

/-! Reconstruct the common factor and product of a pair of denominators
from their prime exponents. -/

namespace FourCorner

/-- Only the prime `2` contributes to the prime factorization of `2`. -/
theorem padicValNat_two_eq {p : ℕ} (hp : p.Prime) :
    padicValNat p 2 = if p = 2 then 1 else 0 := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h : p = 2
  · subst p
    simp only [padicValNat_self, ↓reduceIte]
  · rw [if_neg h]
    exact padicValNat.eq_zero_of_not_dvd
      (fun hd => h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))

/-- Exact primewise minima and sums determine the gcd and product.
The exceptional exponent at `2` is division of `N` by precisely `2`. -/
theorem pair_denominator_assembly {Dp Dm G N : ℕ}
    (hDp : 0 < Dp) (hDm : 0 < Dm) (hG : 0 < G) (hN : 0 < N) (h2 : 2 ∣ N)
    (hmin : ∀ p : ℕ, p.Prime →
      min (padicValNat p Dp) (padicValNat p Dm) = padicValNat p G)
    (hsum : ∀ p : ℕ, p.Prime →
      padicValNat p Dp + padicValNat p Dm =
        padicValNat p N - (if p = 2 then 1 else 0)) :
    Nat.gcd Dp Dm = G ∧ Dp * Dm = N / 2 := by
  constructor
  · apply (Nat.eq_iff_prime_padicValNat_eq _ _
      (Nat.gcd_ne_zero_left hDp.ne') hG.ne').mpr
    intro p hp
    rw [padicValNat_gcd_eq_min hp hDp.ne' hDm.ne']
    exact hmin p hp
  · have hhalf : N / 2 ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd hN h2) (by decide)).ne'
    apply (Nat.eq_iff_prime_padicValNat_eq _ _
      (Nat.mul_ne_zero hDp.ne' hDm.ne') hhalf).mpr
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValNat.mul hDp.ne' hDm.ne', padicValNat.div_of_dvd h2,
      padicValNat_two_eq hp]
    exact hsum p hp

end FourCorner

#print axioms FourCorner.padicValNat_two_eq
#print axioms FourCorner.pair_denominator_assembly
