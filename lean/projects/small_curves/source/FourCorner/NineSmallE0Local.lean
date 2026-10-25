import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace FourCorner.NineSmallE0

private theorem residue_three (a b : ZMod 3) (h : a ^ 2 + b ^ 2 = 0) :
    a = 0 ∧ b = 0 := by
  have hf : ∀ a b : ZMod 3, a ^ 2 + b ^ 2 = 0 → a = 0 ∧ b = 0 := by
    decide +kernel
  exact hf a b h

/-- The ternary form `a² + k b² - 3 s c²` is anisotropic when `k = 1` modulo three
and `s` is a unit modulo three.
The proof is an infinite descent on the sum of the three absolute values. -/
theorem integer_three_anisotropic (k s : ℤ) (hk : (k : ZMod 3) = 1)
    (hs : (s : ZMod 3) ≠ 0)
    (a b c : ℤ) (h : a ^ 2 + k * b ^ 2 = 3 * s * c ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  suffices ∀ n : ℕ, ∀ a b c : ℤ, a.natAbs + b.natAbs + c.natAbs = n →
      a ^ 2 + k * b ^ 2 = 3 * s * c ^ 2 → a = 0 ∧ b = 0 ∧ c = 0 by
    exact this _ a b c rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b c hn heq
    have hmod : (a : ZMod 3) ^ 2 + (b : ZMod 3) ^ 2 = 0 := by
      have hh := congrArg (fun z : ℤ => (z : ZMod 3)) heq
      simpa [hk, show (3 : ZMod 3) = 0 from by decide] using hh
    obtain ⟨ha, hb⟩ := residue_three _ _ hmod
    have had : (3 : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha
    have hbd : (3 : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb
    obtain ⟨a', ha'⟩ := had
    obtain ⟨b', hb'⟩ := hbd
    have hc2 : s * c ^ 2 = 3 * (a' ^ 2 + k * b' ^ 2) := by
      rw [ha', hb'] at heq
      nlinarith [heq]
    have hcd : (3 : ℤ) ∣ c := by
      have hp : Prime (3 : ℤ) := by norm_num
      have hsd : ¬ (3 : ℤ) ∣ s := by
        intro hsd
        exact hs ((ZMod.intCast_zmod_eq_zero_iff_dvd s 3).mpr hsd)
      exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd ⟨a' ^ 2 + k * b' ^ 2, hc2⟩).resolve_left hsd)
    obtain ⟨c', hc'⟩ := hcd
    by_cases hz : a'.natAbs + b'.natAbs + c'.natAbs = 0
    · have ha0 : a' = 0 := Int.natAbs_eq_zero.mp (by omega)
      have hb0 : b' = 0 := Int.natAbs_eq_zero.mp (by omega)
      have hc0 : c' = 0 := Int.natAbs_eq_zero.mp (by omega)
      simp [ha', hb', hc', ha0, hb0, hc0]
    · have hn' : a'.natAbs + b'.natAbs + c'.natAbs < n := by
        rw [ha', hb', hc', Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul] at hn
        norm_num at hn
        omega
      have heq' : a' ^ 2 + k * b' ^ 2 = 3 * s * c' ^ 2 := by
        rw [ha', hb', hc'] at heq
        nlinarith [heq]
      obtain ⟨haa, hbb, hcc⟩ := ih _ hn' a' b' c' rfl heq'
      simp [ha', hb', hc', haa, hbb, hcc]

/-- Rational form of the same local obstruction, after clearing all denominators. -/
theorem rational_three_anisotropic (k s : ℤ) (hk : (k : ZMod 3) = 1)
    (hs : (s : ZMod 3) ≠ 0)
    (a b c : ℚ) (h : a ^ 2 + k * b ^ 2 = 3 * s * c ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  let d : ℚ := a.den * b.den * c.den
  let A : ℤ := a.num * b.den * c.den
  let B : ℤ := b.num * a.den * c.den
  let C : ℤ := c.num * a.den * b.den
  have hd : d ≠ 0 := by
    dsimp [d]
    positivity
  have hA : (A : ℚ) = d * a := by
    dsimp [A, d]
    push_cast
    rw [← Rat.mul_den_eq_num a]
    ring
  have hB : (B : ℚ) = d * b := by
    dsimp [B, d]
    push_cast
    rw [← Rat.mul_den_eq_num b]
    ring
  have hC : (C : ℚ) = d * c := by
    dsimp [C, d]
    push_cast
    rw [← Rat.mul_den_eq_num c]
    ring
  have hi : A ^ 2 + k * B ^ 2 = 3 * s * C ^ 2 := by
    have hq : (A : ℚ) ^ 2 + k * (B : ℚ) ^ 2 = 3 * s * (C : ℚ) ^ 2 := by
      rw [hA, hB, hC]
      linear_combination d ^ 2 * h
    exact_mod_cast hq
  obtain ⟨hAA, hBB, hCC⟩ := integer_three_anisotropic k s hk hs A B C hi
  have ha : d * a = 0 := by rw [← hA, hAA]; norm_num
  have hb : d * b = 0 := by rw [← hB, hBB]; norm_num
  have hc : d * c = 0 := by rw [← hC, hCC]; norm_num
  exact ⟨(mul_eq_zero.mp ha).resolve_left hd,
    (mul_eq_zero.mp hb).resolve_left hd, (mul_eq_zero.mp hc).resolve_left hd⟩

/-- The candidate Kummer row `(1, 3, 3)` is impossible over the rationals. -/
theorem not_row_one_three_three (x a b c : ℚ)
    (h0 : x = a ^ 2) (h1 : x + 1 = 3 * b ^ 2)
    (_h4 : x + 4 = 3 * c ^ 2) : False := by
  have h : a ^ 2 + (1 : ℤ) * (1 : ℚ) ^ 2 = 3 * (1 : ℤ) * b ^ 2 := by
    norm_num
    nlinarith
  have hh := rational_three_anisotropic 1 1 (by norm_num) (by norm_num) a 1 b h
  norm_num at hh

/-- The candidate Kummer row `(2, 1, 2)` is impossible over the rationals. -/
theorem not_row_two_one_two (x a b c : ℚ)
    (h0 : x = 2 * a ^ 2) (h1 : x + 1 = b ^ 2)
    (h4 : x + 4 = 2 * c ^ 2) : False := by
  have h : c ^ 2 + (-2 : ℤ) * b ^ 2 = 3 * (-1 : ℤ) * a ^ 2 := by
    norm_num
    nlinarith
  obtain ⟨hc, hb, ha⟩ := rational_three_anisotropic (-2) (-1) (by decide) (by decide) c b a h
  rw [ha] at h0
  rw [hb] at h1
  norm_num at h0 h1
  linarith

/-- The candidate Kummer row `(-1, -1, 1)` is impossible over the rationals. -/
theorem not_row_neg_one_neg_one_one (x a b c : ℚ)
    (_h0 : x = -a ^ 2) (h1 : x + 1 = -b ^ 2)
    (h4 : x + 4 = c ^ 2) : False := by
  have h : b ^ 2 + (1 : ℤ) * c ^ 2 = 3 * (1 : ℤ) * (1 : ℚ) ^ 2 := by
    norm_num
    nlinarith
  have hh := rational_three_anisotropic 1 1 (by norm_num) (by norm_num) b c 1 h
  norm_num at hh

/-- The candidate Kummer row `(-2, -3, 6)` is impossible over the rationals. -/
theorem not_row_neg_two_neg_three_six (x a b c : ℚ)
    (h0 : x = -2 * a ^ 2) (h1 : x + 1 = -3 * b ^ 2)
    (_h4 : x + 4 = 6 * c ^ 2) : False := by
  have h : (1 : ℚ) ^ 2 + (-2 : ℤ) * a ^ 2 = 3 * (-1 : ℤ) * b ^ 2 := by
    norm_num
    nlinarith
  have hh := rational_three_anisotropic (-2) (-1) (by decide) (by decide) 1 a b h
  norm_num at hh

end FourCorner.NineSmallE0

#print axioms FourCorner.NineSmallE0.integer_three_anisotropic
#print axioms FourCorner.NineSmallE0.rational_three_anisotropic
#print axioms FourCorner.NineSmallE0.not_row_one_three_three
#print axioms FourCorner.NineSmallE0.not_row_two_one_two
#print axioms FourCorner.NineSmallE0.not_row_neg_one_neg_one_one
#print axioms FourCorner.NineSmallE0.not_row_neg_two_neg_three_six
