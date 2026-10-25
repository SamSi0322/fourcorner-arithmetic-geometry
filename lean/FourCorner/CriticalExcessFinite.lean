import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace FourCorner

/-- A square root of a square root of minus one has order eight. -/
theorem critical_excess_eight_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i u : ZMod p} (hi : i ^ 2 = -1) (hu : u ^ 2 = i) : 8 ∣ p - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hneg : (-1 : ZMod p) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hc
  have hu4 : u ^ 4 = -1 := calc
    u ^ 4 = (u ^ 2) ^ 2 := by ring
    _ = -1 := by rw [hu, hi]
  have hu8 : u ^ 8 = 1 := calc
    u ^ 8 = (u ^ 4) ^ 2 := by ring
    _ = 1 := by rw [hu4]; norm_num
  have horder : orderOf u = 8 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 2)
    · simpa [hu4] using hneg
    · simpa using hu8
  have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu8
  simpa only [horder] using ZMod.orderOf_dvd_card_sub_one hu0

/-- One further square root produces an element of order sixteen. -/
theorem critical_excess_sixteen_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i u : ZMod p} (hi : i ^ 2 = -1) (hu : u ^ 2 = i)
    (hs : IsSquare u) : 16 ∣ p - 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hc : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hneg : (-1 : ZMod p) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hc
  obtain ⟨w, hw⟩ := hs
  have hw2 : w ^ 2 = u := by simpa only [pow_two] using hw.symm
  have hw8 : w ^ 8 = -1 := calc
    w ^ 8 = ((w ^ 2) ^ 2) ^ 2 := by ring
    _ = -1 := by rw [hw2, hu, hi]
  have hw16 : w ^ 16 = 1 := calc
    w ^ 16 = (w ^ 8) ^ 2 := by ring
    _ = 1 := by rw [hw8]; norm_num
  have horder : orderOf w = 16 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 3)
    · simpa [hw8] using hneg
    · simpa using hw16
  have hw0 : w ≠ 0 := by intro hz; simp [hz] at hw16
  simpa only [horder] using ZMod.orderOf_dvd_card_sub_one hw0

/-- The square root of `i` gives a square root of two explicitly. -/
theorem critical_excess_two_isSquare {p : ℕ} (i u : ZMod p)
    (hi : i ^ 2 = -1) (hu : u ^ 2 = i) : IsSquare (2 : ZMod p) := by
  refine ⟨u * (1 - i), ?_⟩
  calc
    (2 : ZMod p) = (u * (1 - i)) ^ 2 := by
      linear_combination -(1 - i) ^ 2 * hu - (i - 2) * hi
    _ = (u * (1 - i)) * (u * (1 - i)) := pow_two _


/-- Once the prime is one modulo sixteen, the square root of `1 + i`
forces two to be a fourth-power residue. This uses Fermat's theorem and
`(1 + i)² = 2 i`. -/
theorem critical_excess_quartic_of_sixteen_dvd {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (i v : ZMod p) (hi : i ^ 2 = -1)
    (hv : v ^ 2 = 1 + i) (h16 : 16 ∣ p - 1) :
    (2 : ZMod p) ^ ((p - 1) / 4) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hv0 : v ≠ 0 := by
    intro hz
    have him : i = -1 := by rw [hz] at hv; linear_combination -hv
    have he : (2 : ZMod p) = 0 := by rw [him] at hi; linear_combination hi
    exact htwo he
  obtain ⟨k, hk⟩ := h16
  have hvp : v ^ (16 * k) = 1 := by
    rw [← hk]
    exact ZMod.pow_card_sub_one_eq_one hv0
  have hplus : (1 + i) ^ (8 * k) = 1 := by
    rw [← hv, ← pow_mul]
    convert hvp using 1
    congr 1
    omega
  have hi4 : i ^ 4 = 1 := by
    calc i ^ 4 = (i ^ 2) ^ 2 := by ring
         _ = 1 := by rw [hi]; ring
  have hip : i ^ (4 * k) = 1 := by rw [pow_mul, hi4, one_pow]
  have hprod : (1 + i) ^ 2 = 2 * i := by linear_combination hi
  have hpow : (2 * i) ^ (4 * k) = 1 := by
    rw [← hprod, ← pow_mul]
    convert hplus using 1
    congr 1
    omega
  rw [mul_pow, hip, mul_one] at hpow
  have hexp : (p - 1) / 4 = 4 * k := by omega
  rwa [hexp]


/-- The finite-field restrictions forced by critical excess. Either possible
square class of the product parameter suffices: the square root of `i`
already makes two a square, so a square `2u` also makes `u` a square. -/
theorem critical_excess_residue_conditions {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (i u v : ZMod p) (hi : i ^ 2 = -1)
    (hu : u ^ 2 = i) (hv : v ^ 2 = 1 + i)
    (hs : IsSquare u ∨ IsSquare (2 * u)) :
    p % 16 = 1 ∧ (2 : ZMod p) ^ ((p - 1) / 4) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have htwo_sq : IsSquare (2 : ZMod p) := critical_excess_two_isSquare i u hi hu
  have hu_sq : IsSquare u := by
    rcases hs with hs | hs
    · exact hs
    · simpa only [mul_div_cancel_left₀ u htwo] using hs.div htwo_sq
  have h16 : 16 ∣ p - 1 := critical_excess_sixteen_dvd hp hp2 hi hu hu_sq
  refine ⟨?_, critical_excess_quartic_of_sixteen_dvd hp hp2 i v hi hv h16⟩
  have hp_pos := hp.pos
  omega

end FourCorner

#print axioms FourCorner.critical_excess_quartic_of_sixteen_dvd

#print axioms FourCorner.critical_excess_eight_dvd
#print axioms FourCorner.critical_excess_sixteen_dvd
#print axioms FourCorner.critical_excess_two_isSquare
#print axioms FourCorner.critical_excess_residue_conditions
