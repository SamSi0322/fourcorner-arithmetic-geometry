import FourCorner.CommonRootMatrixLinear
import FourCorner.CommonRootMatrixMask
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum

namespace FourCorner

/-- The additive quadratic-character bit, with the row prime as denominator. -/
def legendreBit (p : ℕ) [Fact p.Prime] (a : ℤ) : ZMod 2 :=
  if legendreSym p a = -1 then 1 else 0

theorem legendreBit_eq_zero_iff (p : ℕ) [Fact p.Prime] {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) : legendreBit p a = 0 ↔ legendreSym p a = 1 := by
  rcases legendreSym.eq_one_or_neg_one p ha with h | h <;> simp [legendreBit, h]

theorem legendreBit_eq_one_iff (p : ℕ) [Fact p.Prime] (a : ℤ) :
    legendreBit p a = 1 ↔ legendreSym p a = -1 := by
  by_cases h : legendreSym p a = -1 <;> simp [legendreBit, h]

@[simp] theorem legendreBit_one (p : ℕ) [Fact p.Prime] : legendreBit p 1 = 0 := by
  simp [legendreBit]

theorem legendreBit_mul (p : ℕ) [Fact p.Prime] {a b : ℤ}
    (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0) :
    legendreBit p (a * b) = legendreBit p a + legendreBit p b := by
  rcases legendreSym.eq_one_or_neg_one p ha with ha | ha <;>
    rcases legendreSym.eq_one_or_neg_one p hb with hb | hb <;>
    norm_num [legendreBit, legendreSym.mul, ha, hb]; decide

theorem legendreBit_sq (p : ℕ) [Fact p.Prime] {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) : legendreBit p (a ^ 2) = 0 := by
  simp [legendreBit, legendreSym.sq_one' p ha]

theorem legendreBit_pow (p : ℕ) [Fact p.Prime] {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) (k : ℕ) :
    legendreBit p (a ^ k) = (k : ZMod 2) * legendreBit p a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, legendreBit_mul p (by simpa using pow_ne_zero k ha) ha, ih]
    push_cast
    ring

/-- The bit of `2` vanishes at all primes in the allowed kernel support. -/
theorem legendreBit_two (p : ℕ) [Fact p.Prime]
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) : legendreBit p 2 = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp2
  have hsym : legendreSym p 2 = 1 := by
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases hp8 with hp8 | hp8 <;> simp [hp8, hpodd]
  simp [legendreBit, hsym]

/-- Multiplication of nonzero factors becomes addition of their character bits. -/
theorem legendreBit_prod {ι : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset ι) (a : ι → ℤ) (ha : ∀ i ∈ s, (a i : ZMod p) ≠ 0) :
    legendreBit p (∏ i ∈ s, a i) = ∑ i ∈ s, legendreBit p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [legendreBit_mul p (ha i (Finset.mem_insert_self i s))]
    · rw [ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))]
    · push_cast
      exact Finset.prod_ne_zero_iff.mpr (fun j hj => ha j (Finset.mem_insert_of_mem hj))

/-- A multiplicative character condition is exactly the additive parity row. -/
theorem legendreBit_product_pow_eq_zero_iff {ι : Type*} (p : ℕ) [Fact p.Prime]
    (s : Finset ι) (a : ι → ℤ) (e : ι → ℕ)
    (ha : ∀ i ∈ s, (a i : ZMod p) ≠ 0) :
    (∑ i ∈ s, (e i : ZMod 2) * legendreBit p (a i)) = 0 ↔
      legendreSym p (∏ i ∈ s, a i ^ e i) = 1 := by
  have hpow : ∀ i ∈ s, ((a i ^ e i : ℤ) : ZMod p) ≠ 0 := by
    intro i hi
    simpa using pow_ne_zero (e i) (ha i hi)
  have hprod : ((∏ i ∈ s, a i ^ e i : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => by simpa using hpow i hi)
  rw [← legendreBit_eq_zero_iff p hprod, legendreBit_prod p s (fun i => a i ^ e i) hpow]
  have heq := Finset.sum_congr rfl (fun i hi => legendreBit_pow p (ha i hi) (e i))
  rw [heq]

/-- Legendre entries have the row prime in the denominator. No symmetry is imposed. -/
def primeLegendreEntries {r : ℕ} (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) :
    Matrix (Fin r) (Fin r) (ZMod 2) :=
  fun i j => @legendreBit (p i) ⟨hp i⟩ (p j)

/-- The arithmetic matrix with its prescribed row-sum diagonal. -/
def primeLegendreMatrix {r : ℕ} (p : Fin r → ℕ) (hp : ∀ i, (p i).Prime) :
    Matrix (Fin r) (Fin r) (ZMod 2) := rowZeroMatrix (primeLegendreEntries p hp)

private theorem distinct_prime_cast_ne_zero {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) {i j : Fin r}
    (hij : i ≠ j) : ((p j : ℤ) : ZMod (p i)) ≠ 0 := by
  intro hz
  have hdiv : p i ∣ p j := by
    exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  exact hij (hinj (((hp j).dvd_iff_eq (hp i).ne_one).mp hdiv).symm)

theorem primeLegendreMatrix_off_diagonal_zero_iff {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) {i j : Fin r}
    (hij : i ≠ j) :
    primeLegendreMatrix p hp i j = 0 ↔ @legendreSym (p i) ⟨hp i⟩ (p j) = 1 := by
  rw [primeLegendreMatrix, rowZeroMatrix_off_diagonal _ hij]
  exact @legendreBit_eq_zero_iff (p i) ⟨hp i⟩ (p j)
    (distinct_prime_cast_ne_zero p hp hinj hij)

theorem primeLegendreMatrix_off_diagonal_one_iff {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) {i j : Fin r} (hij : i ≠ j) :
    primeLegendreMatrix p hp i j = 1 ↔ @legendreSym (p i) ⟨hp i⟩ (p j) = -1 := by
  rw [primeLegendreMatrix, rowZeroMatrix_off_diagonal _ hij]
  exact @legendreBit_eq_one_iff (p i) ⟨hp i⟩ (p j)

/-- At an unselected prime the bit of the mask product is the sum of the
 selected off-diagonal Legendre entries. -/
theorem legendreBit_maskProduct {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (e : Fin r → ZMod 2) (i : Fin r) (hei : e i = 0) :
    @legendreBit (p i) ⟨hp i⟩ (commonRootMaskProduct p e) =
      ∑ j ∈ Finset.univ.erase i, primeLegendreEntries p hp i j * e j := by
  have : Fact (p i).Prime := ⟨hp i⟩
  have hmask : (commonRootMaskProduct p e : ℤ) =
      ∏ j ∈ Finset.univ.erase i, if e j = 1 then (p j : ℤ) else 1 := by
    simp only [commonRootMaskProduct, Nat.cast_prod]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp [hei]
  rw [hmask]
  have hnon : ∀ j ∈ Finset.univ.erase i,
      ((if e j = 1 then (p j : ℤ) else 1 : ℤ) : ZMod (p i)) ≠ 0 := by
    intro j hj
    by_cases hej : e j = 1
    · simpa [hej] using distinct_prime_cast_ne_zero p hp hinj
        (Ne.symm (Finset.mem_erase.mp hj).1)
    · simp [hej]
  rw [legendreBit_prod (p i) _ _ hnon]
  apply Finset.sum_congr rfl
  intro j hj
  rcases commonRoot_zmod_two_cases (e j) with hej | hej <;>
    simp [hej, primeLegendreEntries]

/-- The selected/complementary local character alternatives imply the actual
 arithmetic matrix row equation. -/
theorem primeLegendreMatrix_row_eq_zero_of_local {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (e : Fin r → ZMod 2) (i : Fin r)
    (hlocal :
      (e i = 0 ∧ @legendreSym (p i) ⟨hp i⟩ (commonRootMaskProduct p e) = 1) ∨
      (e i = 1 ∧ @legendreSym (p i) ⟨hp i⟩
        (commonRootMaskProduct p (commonRootMaskComplement e)) = 1)) :
    (primeLegendreMatrix p hp).mulVec e i = 0 := by
  rw [primeLegendreMatrix, rowZeroMatrix_mulVec]
  rcases hlocal with ⟨hei, hsym⟩ | ⟨hei, hsym⟩
  · simp only [hei, add_zero]
    rw [← legendreBit_maskProduct p hp hinj e i hei]
    simp [legendreBit, hsym]
  · have hcomp : commonRootMaskComplement e i = 0 := by
      simp only [commonRootMaskComplement, hei]
      decide
    have hbit := legendreBit_maskProduct p hp hinj (commonRootMaskComplement e) i hcomp
    have hzero : @legendreBit (p i) ⟨hp i⟩
        (commonRootMaskProduct p (commonRootMaskComplement e)) = 0 := by
      simp [legendreBit, hsym]
    rw [hzero] at hbit
    simpa [hei, commonRootMaskComplement, add_comm] using hbit.symm

/-- Local selected/complementary quadratic characters at all row primes put
 the mask in the kernel of the explicitly defined arithmetic matrix. -/
theorem primeLegendreMatrix_mulVec_eq_zero_of_local {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (e : Fin r → ZMod 2)
    (hlocal : ∀ i,
      (e i = 0 ∧ @legendreSym (p i) ⟨hp i⟩ (commonRootMaskProduct p e) = 1) ∨
      (e i = 1 ∧ @legendreSym (p i) ⟨hp i⟩
        (commonRootMaskProduct p (commonRootMaskComplement e)) = 1)) :
    (primeLegendreMatrix p hp).mulVec e = 0 := by
  funext i
  exact primeLegendreMatrix_row_eq_zero_of_local p hp hinj e i (hlocal i)

end FourCorner

#print axioms FourCorner.legendreBit_mul
#print axioms FourCorner.primeLegendreMatrix_mulVec_eq_zero_of_local
