import FourCorner.RamifiedUnits

set_option autoImplicit false

namespace FourCorner

/-- For a prime congruent to one modulo eight, the character of either square root
of two is the ramified sign times the eighth-power parity sign. -/
theorem sqrt_two_character_one {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 1) {iota a : ZMod p}
    (hiota : iota ^ 2 = -1) (ha : a ^ 2 = 2) :
    quadraticChar (ZMod p) a =
      quadraticChar (ZMod p) (1 + iota) * (-1 : ℤ) ^ ((p - 1) / 8) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have ha0 : a ≠ 0 := by
    intro hz
    exact Ring.two_ne_zero hchar (by simpa [hz] using ha.symm)
  have hEuler : (quadraticChar (ZMod p) a : ZMod p) =
      (2 : ZMod p) ^ ((p - 1) / 4) := by
    rw [quadraticChar_eq_pow_of_char_ne_two' hchar, ZMod.card]
    have hhalf : p / 2 = 2 * ((p - 1) / 4) := by omega
    rw [hhalf, pow_mul, ha]
  have hCast : (quadraticChar (ZMod p) a : ZMod p) =
      ((quadraticChar (ZMod p) (1 + iota) * (-1 : ℤ) ^ ((p - 1) / 8) : ℤ) : ZMod p) := by
    rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      ramified_quartic_sign hp hiota, hEuler, mul_assoc, ← pow_two]
    simp only [← pow_mul]
    rw [Nat.mul_comm ((p - 1) / 8) 2, pow_mul]
    norm_num
  apply Int.cast_injOn_of_ringChar_ne_two hchar (x₁ := quadraticChar (ZMod p) a)
    (x₂ := quadraticChar (ZMod p) (1 + iota) * (-1 : ℤ) ^ ((p - 1) / 8))
  · rcases quadraticChar_dichotomy ha0 with h | h <;> simp [h]
  · rcases ramified_sign_dichotomy hp hiota with h | h <;>
      rcases neg_one_pow_eq_or ℤ ((p - 1) / 8) with hs | hs <;> simp [h, hs]
  · exact hCast

end FourCorner

#print axioms FourCorner.sqrt_two_character_one
