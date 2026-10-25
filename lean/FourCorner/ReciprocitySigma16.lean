import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace FourCorner

/-- The sign character on the residues `1, 7, 9, 15` modulo `16`. -/
def sigma16 (n : ℕ) : ℤ := if n % 16 = 1 ∨ n % 16 = 15 then 1 else -1

@[simp] lemma sigma16_one : sigma16 1 = 1 := by norm_num [sigma16]

lemma sigma16_eq_one_or_neg_one (n : ℕ) : sigma16 n = 1 ∨ sigma16 n = -1 := by
  unfold sigma16
  split_ifs <;> simp

lemma mod_eight_mul_of_one_or_seven {a b : ℕ}
    (ha : a % 8 = 1 ∨ a % 8 = 7) (hb : b % 8 = 1 ∨ b % 8 = 7) :
    (a * b) % 8 = 1 ∨ (a * b) % 8 = 7 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    norm_num [Nat.mul_mod, ha, hb]

lemma sigma16_mul {a b : ℕ}
    (ha : a % 8 = 1 ∨ a % 8 = 7) (hb : b % 8 = 1 ∨ b % 8 = 7) :
    sigma16 (a * b) = sigma16 a * sigma16 b := by
  have ha16 : a % 16 = 1 ∨ a % 16 = 7 ∨ a % 16 = 9 ∨ a % 16 = 15 := by omega
  have hb16 : b % 16 = 1 ∨ b % 16 = 7 ∨ b % 16 = 9 ∨ b % 16 = 15 := by omega
  rcases ha16 with ha | ha | ha | ha <;>
    rcases hb16 with hb | hb | hb | hb <;>
    norm_num [sigma16, Nat.mul_mod, ha, hb]

lemma mod_eight_finset_prod_of_one_or_seven {α : Type*} (s : Finset α) (f : α → ℕ)
    (hs : ∀ i ∈ s, f i % 8 = 1 ∨ f i % 8 = 7) :
    (∏ i ∈ s, f i) % 8 = 1 ∨ (∏ i ∈ s, f i) % 8 = 7 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mod_eight_mul_of_one_or_seven (hs a (Finset.mem_insert_self a s))
        (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)))

lemma sigma16_finset_prod {α : Type*} (s : Finset α) (f : α → ℕ)
    (hs : ∀ i ∈ s, f i % 8 = 1 ∨ f i % 8 = 7) :
    sigma16 (∏ i ∈ s, f i) = ∏ i ∈ s, sigma16 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hs' : ∀ i ∈ s, f i % 8 = 1 ∨ f i % 8 = 7 :=
        fun i hi => hs i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        sigma16_mul (hs a (Finset.mem_insert_self a s))
          (mod_eight_finset_prod_of_one_or_seven s f hs'), ih hs']

lemma sigma16_primeFactors_prod {n : ℕ} (hn : Squarefree n)
    (hs : ∀ p ∈ n.primeFactors, p % 8 = 1 ∨ p % 8 = 7) :
    sigma16 n = ∏ p ∈ n.primeFactors, sigma16 p := by
  simpa only [id_eq, Nat.prod_primeFactors_of_squarefree hn] using
    sigma16_finset_prod n.primeFactors id hs

lemma mod_eight_pow_of_one_or_seven {a : ℕ}
    (ha : a % 8 = 1 ∨ a % 8 = 7) (k : ℕ) :
    (a ^ k) % 8 = 1 ∨ (a ^ k) % 8 = 7 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      exact mod_eight_mul_of_one_or_seven ih ha

lemma sigma16_pow {a : ℕ} (ha : a % 8 = 1 ∨ a % 8 = 7) (k : ℕ) :
    sigma16 (a ^ k) = sigma16 a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, sigma16_mul (mod_eight_pow_of_one_or_seven ha k) ha,
        ih, pow_succ]

lemma sigma16_pow_mod_two {a : ℕ} (ha : a % 8 = 1 ∨ a % 8 = 7) (k : ℕ) :
    sigma16 (a ^ k) = sigma16 a ^ (k % 2) := by
  rw [sigma16_pow ha]
  rcases sigma16_eq_one_or_neg_one a with h | h
  · simp [h]
  · simpa only [h] using neg_one_pow_eq_pow_mod_two (R := ℤ) k

lemma sigma16_pow_parity {a : ℕ} (ha : a % 8 = 1 ∨ a % 8 = 7) (k : ℕ) :
    sigma16 (a ^ k) = if k % 2 = 0 then 1 else sigma16 a := by
  rw [sigma16_pow_mod_two ha]
  by_cases hk : k % 2 = 0
  · simp [hk]
  · have hk' : k % 2 = 1 := by omega
    simp [hk']

/-- The exponent formula on the residue class `1` modulo `8`. -/
lemma sigma16_of_mod_eight_eq_one {n : ℕ} (hn : n % 8 = 1) :
    sigma16 n = (-1 : ℤ) ^ ((n - 1) / 8) := by
  rw [neg_one_pow_eq_pow_mod_two]
  have hn16 : n % 16 = 1 ∨ n % 16 = 9 := by omega
  rcases hn16 with hn16 | hn16
  · have he : ((n - 1) / 8) % 2 = 0 := by omega
    norm_num [sigma16, hn16, he]
  · have he : ((n - 1) / 8) % 2 = 1 := by omega
    norm_num [sigma16, hn16, he]

/-- The exponent formula on the residue class `7` modulo `8`. -/
lemma sigma16_of_mod_eight_eq_seven {n : ℕ} (hn : n % 8 = 7) :
    sigma16 n = (-1 : ℤ) ^ ((n + 1) / 8) := by
  rw [neg_one_pow_eq_pow_mod_two]
  have hn16 : n % 16 = 7 ∨ n % 16 = 15 := by omega
  rcases hn16 with hn16 | hn16
  · have he : ((n + 1) / 8) % 2 = 1 := by omega
    norm_num [sigma16, hn16, he]
  · have he : ((n + 1) / 8) % 2 = 0 := by omega
    norm_num [sigma16, hn16, he]

end FourCorner
