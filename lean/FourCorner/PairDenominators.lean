import FourCorner.PairOddVal
import FourCorner.PairOddFactors
import FourCorner.PairDyadic
import FourCorner.PairDenAssembly

namespace FourCorner
namespace IntegralModel

/-- The labelled positive rational radius of an actual primitive integral model. -/
def pairRationalRadius (M : IntegralModel) (i : Fin 4) : ℚ :=
  (M.pairRadius i : ℚ) / M.L

/-- Reduced denominator of the sum of two labelled radii. -/
def pairPlusDen (M : IntegralModel) (i j : Fin 4) : ℕ :=
  (M.pairRationalRadius i + M.pairRationalRadius j).den

/-- Reduced denominator of the difference of two labelled radii. -/
def pairMinusDen (M : IntegralModel) (i j : Fin 4) : ℕ :=
  (M.pairRationalRadius i - M.pairRationalRadius j).den

theorem pairPlusDen_eq (M : IntegralModel) (i j : Fin 4) :
    M.pairPlusDen i j = (((M.pairRadius i + M.pairRadius j : ℤ) : ℚ) / M.L).den := by
  simp [pairPlusDen, pairRationalRadius, add_div]

theorem pairMinusDen_eq (M : IntegralModel) (i j : Fin 4) :
    M.pairMinusDen i j = (((M.pairRadius i - M.pairRadius j : ℤ) : ℚ) / M.L).den := by
  simp [pairMinusDen, pairRationalRadius, sub_div]

theorem reduced_pairRadius_units (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (hh : (p : ℤ) ∣ M.reducedSide) (i : Fin 4) :
    ¬ (p : ℤ) ∣ M.pairRadius i / (M.radiusContent : ℤ) := by
  have h := M.normalized_radii_units hp hh
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- Exact odd-prime depths, for every pair of distinct corner labels. -/
theorem pair_den_odd_valuations (M : IntegralModel) {i j : Fin 4}
    (hij : i ≠ j) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    min (padicValNat p (M.pairPlusDen i j)) (padicValNat p (M.pairMinusDen i j)) =
      padicValNat p M.radiusContent ∧
    padicValNat p (M.pairPlusDen i j) + padicValNat p (M.pairMinusDen i j) =
      padicValNat p M.L.natAbs := by
  rw [M.pairPlusDen_eq, M.pairMinusDen_eq]
  have hs : M.pairRadius i + M.pairRadius j ≠ 0 :=
    ne_of_gt (add_pos (M.pairRadius_pos i) (M.pairRadius_pos j))
  have hd : M.pairRadius i - M.pairRadius j ≠ 0 := sub_ne_zero.mpr (M.pairRadius_ne hij)
  have hG : (M.radiusContent : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt M.radiusContent_pos)
  have h := odd_pair_den_values hp hodd (M.pairRadius i) (M.pairRadius j)
    M.L (M.radiusContent : ℤ) M.reducedSide (M.pairDifferenceFactor j i)
    (ne_of_gt (M.pairRadius_pos i)) (ne_of_gt (M.pairRadius_pos j))
    (ne_of_gt M.L_pos) hG (ne_of_gt M.reducedSide_pos) hs hd
    M.reducedSide_factorization (M.radiusContent_dvd_pairRadius i)
    (M.radiusContent_dvd_pairRadius j)
    (fun hh => ⟨M.reduced_pairRadius_units hp hh i, M.reduced_pairRadius_units hp hh j⟩)
    (M.pairRadius_sq_sub j i)
    (fun hg => M.radiusContent_prime_not_dvd_pairDifferenceFactor hp
      (Int.natCast_dvd_natCast.mp hg) (Ne.symm hij))
  simpa using h

/-- Exact two-adic depths, without choosing an orientation of the square. -/
theorem pair_den_two_valuations (M : IntegralModel) {i j : Fin 4}
    (hij : i ≠ j) :
    min (padicValNat 2 (M.pairPlusDen i j)) (padicValNat 2 (M.pairMinusDen i j)) = 0 ∧
    padicValNat 2 (M.pairPlusDen i j) + padicValNat 2 (M.pairMinusDen i j) =
      padicValNat 2 M.L.natAbs - 1 := by
  rw [M.pairPlusDen_eq, M.pairMinusDen_eq]
  have h := odd_pair_den_two_valuation
    (M.pairRadius_odd i) (M.pairRadius_odd j) M.L_pos
    (Int.dvd_of_emod_eq_zero M.eight_divides_L)
    (M.two_mul_L_dvd_pairRadius_sq_sub j i) (M.pairRadius_ne hij)
    (ne_of_gt (add_pos (M.pairRadius_pos i) (M.pairRadius_pos j)))
  exact ⟨h.2,h.1⟩

/-- Theorem thm:int:pair-denominators: the two reduced denominators have
common content G and product L/2, uniformly for all six distinct corner pairs. -/
theorem pair_denominators (M : IntegralModel) {i j : Fin 4} (hij : i ≠ j) :
    Nat.gcd (M.pairPlusDen i j) (M.pairMinusDen i j) = M.radiusContent ∧
    M.pairPlusDen i j * M.pairMinusDen i j = M.L.natAbs / 2 := by
  have h2 : 2 ∣ M.L.natAbs :=
    Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  apply pair_denominator_assembly (Rat.den_pos _) (Rat.den_pos _)
    M.radiusContent_pos (Int.natAbs_pos.mpr (ne_of_gt M.L_pos)) h2
  · intro p hp
    by_cases he : p = 2
    · subst p
      have hg := padicValNat.eq_zero_of_not_dvd M.radiusContent_odd
      rw [hg]
      exact (M.pair_den_two_valuations hij).1
    · exact (M.pair_den_odd_valuations hij hp he).1
  · intro p hp
    by_cases he : p = 2
    · subst p
      simpa [pairPlusDen, pairMinusDen] using (M.pair_den_two_valuations hij).2
    · simpa [pairPlusDen, pairMinusDen, he] using (M.pair_den_odd_valuations hij hp he).2

/-- The same conclusion with the literal integer quotient L/2. -/
theorem pair_denominators_literal (M : IntegralModel) {i j : Fin 4} (hij : i ≠ j) :
    Nat.gcd (M.pairPlusDen i j) (M.pairMinusDen i j) = M.radiusContent ∧
    M.pairPlusDen i j * M.pairMinusDen i j = (M.L / 2).natAbs := by
  have h2 : (2 : ℤ) ∣ M.L := Int.dvd_of_emod_eq_zero M.basic_mod_four.1
  simpa [Int.natAbs_ediv_of_dvd h2] using M.pair_denominators hij

end IntegralModel
end FourCorner
#print axioms FourCorner.IntegralModel.pair_den_odd_valuations
#print axioms FourCorner.IntegralModel.pair_den_two_valuations
#print axioms FourCorner.IntegralModel.pair_denominators

#print axioms FourCorner.IntegralModel.pair_denominators_literal
