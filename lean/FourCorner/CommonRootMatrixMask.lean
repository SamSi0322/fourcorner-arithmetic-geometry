import FourCorner.CommonRootMatrixMaskSupport
import Mathlib.Data.ZMod.Basic

namespace FourCorner

open scoped BigOperators

/-- Product of the primes selected by a binary mask. -/
def commonRootMaskProduct {r : ℕ} (p : Fin r → ℕ) (e : Fin r → ZMod 2) : ℕ :=
  ∏ i, if e i = 1 then p i else 1

/-- Complement of a binary mask. -/
def commonRootMaskComplement {r : ℕ} (e : Fin r → ZMod 2) : Fin r → ZMod 2 :=
  fun i => 1 + e i

lemma commonRoot_zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h := ZMod.val_lt a
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  rcases ha with ha | ha
  · left
    exact ZMod.val_injective 2 (by norm_num [ha, ZMod.val_one_eq_one_mod])
  · right
    exact ZMod.val_injective 2 (by norm_num [ha, ZMod.val_one_eq_one_mod])

lemma commonRootMaskComplement_eq_one_iff {r : ℕ} (e : Fin r → ZMod 2) (i : Fin r) :
    commonRootMaskComplement e i = 1 ↔ e i = 0 := by
  rcases commonRoot_zmod_two_cases (e i) with h | h <;> simp [commonRootMaskComplement, h]

theorem commonRootMaskProduct_complement_mul {r : ℕ} (p : Fin r → ℕ)
    (e : Fin r → ZMod 2) :
    commonRootMaskProduct p e * commonRootMaskProduct p (commonRootMaskComplement e) =
      ∏ i, p i := by
  rw [commonRootMaskProduct, commonRootMaskProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rcases commonRoot_zmod_two_cases (e i) with h | h <;> simp [commonRootMaskComplement, h]

theorem commonRootMaskProduct_dvd {r : ℕ} (p : Fin r → ℕ) (e : Fin r → ZMod 2) :
    commonRootMaskProduct p e ∣ ∏ i, p i := by
  rw [← commonRootMaskProduct_complement_mul p e]
  exact dvd_mul_right _ _

theorem commonRootMaskProduct_prime_dvd_iff {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (e : Fin r → ZMod 2) (i : Fin r) :
    p i ∣ commonRootMaskProduct p e ↔ e i = 1 := by
  rw [commonRootMaskProduct, (hp i).prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨j, hj, hd⟩
    split_ifs at hd with he
    · have hij : i = j := hpi (((hp j).dvd_iff_eq (hp i).ne_one).mp hd).symm
      simpa [hij] using he
    · exact False.elim ((hp i).not_dvd_one hd)
  · intro he
    exact ⟨i, Finset.mem_univ i, by simp [he]⟩

theorem commonRootMaskProduct_complement_prime_dvd_iff {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (e : Fin r → ZMod 2) (i : Fin r) :
    p i ∣ commonRootMaskProduct p (commonRootMaskComplement e) ↔ e i = 0 := by
  rw [commonRootMaskProduct_prime_dvd_iff p hp hpi,
    commonRootMaskComplement_eq_one_iff]

theorem commonRootPrimeProduct_squarefree {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p) :
    Squarefree (∏ i, p i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    apply Nat.coprime_iff_isRelPrime.mp
    exact (hp i).coprime_iff_not_dvd.mpr (fun hd =>
      hij (hpi (((hp j).dvd_iff_eq (hp i).ne_one).mp hd).symm))
  · intro i hi
    exact (hp i).squarefree

theorem commonRootMaskProduct_squarefree {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p)
    (e : Fin r → ZMod 2) : Squarefree (commonRootMaskProduct p e) :=
  (commonRootPrimeProduct_squarefree p hp hpi).squarefree_of_dvd
    (commonRootMaskProduct_dvd p e)

/-- Every selected product is odd when none of the listed primes is `2`. -/
theorem commonRootMaskProduct_two_not_dvd {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hne : ∀ i, p i ≠ 2)
    (e : Fin r → ZMod 2) : ¬ 2 ∣ commonRootMaskProduct p e := by
  rw [commonRootMaskProduct, Nat.prime_two.prime.dvd_finsetProd_iff]
  rintro ⟨i, hi, hd⟩
  split_ifs at hd with he
  · exact hne i (((hp i).dvd_iff_eq (by decide : 2 ≠ 1)).mp hd)
  · exact Nat.prime_two.not_dvd_one hd

theorem commonRootMaskProduct_twice_squarefree {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p) (hne : ∀ i, p i ≠ 2)
    (e : Fin r → ZMod 2) : Squarefree (2 * commonRootMaskProduct p e) := by
  rw [Nat.squarefree_mul_iff]
  exact ⟨Nat.prime_two.coprime_iff_not_dvd.mpr
    (commonRootMaskProduct_two_not_dvd p hp hne e), Nat.prime_two.squarefree,
    commonRootMaskProduct_squarefree p hp hpi e⟩

/-- Squarefree support gives an exact finite prime mask, including the factor `2`. -/
theorem commonRootMaskProduct_exists_of_squarefree {r n : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (hpi : Function.Injective p) (hne : ∀ i, p i ≠ 2)
    (hn : Squarefree n) (h2 : 2 ∣ n)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ n → q = 2 ∨ ∃ i, q = p i) :
    ∃ e : Fin r → ZMod 2, n = 2 * commonRootMaskProduct p e := by
  classical
  refine ⟨fun i => if p i ∣ n then 1 else 0, ?_⟩
  calc
    n = 2 * ∏ i ∈ Finset.univ.filter (fun i => p i ∣ n), p i :=
      squarefree_even_eq_two_mul_prod_dvd p hp hpi hne hn h2 hsupport
    _ = 2 * commonRootMaskProduct p (fun i => if p i ∣ n then 1 else 0) := by
      congr 1
      rw [commonRootMaskProduct, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hd : p i ∣ n <;> simp [hd]

/-- The indicator definition is the conventional product with binary exponents. -/
theorem commonRootMaskProduct_eq_prod_pow {r : ℕ} (p : Fin r → ℕ)
    (e : Fin r → ZMod 2) :
    commonRootMaskProduct p e = ∏ i, p i ^ (e i).val := by
  unfold commonRootMaskProduct
  apply Finset.prod_congr rfl
  intro i hi
  rcases commonRoot_zmod_two_cases (e i) with h | h <;>
    simp [h, ZMod.val_one_eq_one_mod]

theorem commonRootMaskProduct_pos {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (e : Fin r → ZMod 2) :
    0 < commonRootMaskProduct p e := by
  unfold commonRootMaskProduct
  apply Finset.prod_pos
  intro i hi
  split_ifs
  · exact (hp i).pos
  · exact Nat.zero_lt_one

theorem commonRootMaskProduct_ne_zero {r : ℕ} (p : Fin r → ℕ)
    (hp : ∀ i, (p i).Prime) (e : Fin r → ZMod 2) :
    commonRootMaskProduct p e ≠ 0 :=
  (commonRootMaskProduct_pos p hp e).ne'

end FourCorner
