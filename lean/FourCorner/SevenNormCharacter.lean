import FourCorner.GaussianModFrobenius
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

set_option autoImplicit false

namespace FourCorner

private lemma gaussianMod_eighth_pow_of_opposite {p : ℕ} (x y : ZMod p)
    (hxy : (x ^ 2 - y ^ 2) ^ 2 = (2 * x * y) ^ 2) :
    (⟨x, y⟩ : GaussianMod p) ^ 8 =
      algebraMap (ZMod p) (GaussianMod p) (-(x ^ 2 + y ^ 2) ^ 4) := by
  let a := x ^ 2 - y ^ 2
  let b := 2 * x * y
  have hab : a ^ 2 = b ^ 2 := hxy
  have hs : (⟨x, y⟩ : GaussianMod p) ^ 2 = ⟨a, b⟩ := by
    ext <;> simp [pow_two, a, b] <;> ring
  have hfour : (⟨x, y⟩ : GaussianMod p) ^ 4 = ⟨0, 2 * a * b⟩ := by
    rw [show (4:ℕ) = 2 * 2 by rfl, pow_mul, hs]
    ext <;> simp [pow_two]
    · linear_combination hab
    · ring
  have hn : (x ^ 2 + y ^ 2) ^ 2 = a ^ 2 + b ^ 2 := by dsimp [a, b]; ring
  have hn4 : (x ^ 2 + y ^ 2) ^ 4 = (2 * a * b) ^ 2 := by
    calc
      _ = ((x ^ 2 + y ^ 2) ^ 2) ^ 2 := by ring
      _ = (a ^ 2 + b ^ 2) ^ 2 := by rw [hn]
      _ = (2 * a * b) ^ 2 := by linear_combination (a ^ 2 - b ^ 2) * hab
  rw [show (8:ℕ) = 4 * 2 by rfl, pow_mul, hfour, pow_two]
  apply QuadraticAlgebra.ext
  · change 0 * 0 + (-1) * (2 * a * b) * (2 * a * b) = -(x ^ 2 + y ^ 2) ^ 4
    linear_combination hn4
  · change 0 * (2 * a * b) + (2 * a * b) * 0 + 0 * (2 * a * b) * (2 * a * b) = 0
    ring

/-- The norm character of an opposite-corner Gaussian square at a prime
congruent to seven modulo eight. -/
theorem seven_opposite_norm_character {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 7) (x y : ZMod p) (hn : x ^ 2 + y ^ 2 ≠ 0)
    (hxy : (x ^ 2 - y ^ 2) ^ 2 = (2 * x * y) ^ 2) :
    quadraticChar (ZMod p) (x ^ 2 + y ^ 2) = (-1 : ℤ) ^ ((p + 1) / 8) := by
  let k := (p + 1) / 8
  let a := x ^ 2 + y ^ 2
  have ha : a ≠ 0 := hn
  have hk : p + 1 = 8 * k := by dsimp [k]; omega
  have hk2 : 4 * k = p / 2 + 1 := by dsimp [k]; omega
  have hz := gaussianMod_pow_prime_add_one (show p % 4 = 3 by omega) x y
  have he := gaussianMod_eighth_pow_of_opposite x y hxy
  rw [hk, pow_mul, he, ← map_pow] at hz
  have hs : (-a ^ 4) ^ k = a := QuadraticAlgebra.algebraMap_injective hz
  have hm : (-1 : ZMod p) ^ k * a ^ (p / 2) = 1 := by
    apply (mul_right_cancel₀ ha)
    calc
      _ = (-1 : ZMod p) ^ k * a ^ (p / 2 + 1) := by rw [pow_add, pow_one]; ring
      _ = (-1 : ZMod p) ^ k * a ^ (4 * k) := by rw [hk2]
      _ = (-a ^ 4) ^ k := by rw [pow_mul, ← mul_pow]; congr 1; ring
      _ = 1 * a := by simpa using hs
  have heuler : a ^ (p / 2) = (-1 : ZMod p) ^ k := by
    calc
      _ = ((-1 : ZMod p) ^ k) ^ 2 * a ^ (p / 2) := by rw [← pow_mul, Nat.mul_comm k 2, pow_mul]; simp
      _ = (-1 : ZMod p) ^ k * ((-1 : ZMod p) ^ k * a ^ (p / 2)) := by ring
      _ = (-1 : ZMod p) ^ k := by rw [hm, mul_one]
  have hc : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  rw [quadraticChar_eq_pow_of_char_ne_two hc hn, ZMod.card, heuler]
  rcases neg_one_pow_eq_or ℤ k with h | h
  · have hf : (-1 : ZMod p) ^ k = 1 := by simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using congrArg (fun n : ℤ => (n : ZMod p)) h
    simpa only [hf, if_true] using h.symm
  · have hf : (-1 : ZMod p) ^ k = -1 := by simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using congrArg (fun n : ℤ => (n : ZMod p)) h
    have hne : (-1 : ZMod p) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hc
    simpa only [hf, if_neg hne] using h.symm

end FourCorner
