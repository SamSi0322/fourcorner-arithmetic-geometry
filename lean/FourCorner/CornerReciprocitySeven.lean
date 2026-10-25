import FourCorner.PairSupport
import FourCorner.RamifiedUnits
import FourCorner.SevenNormCharacter

set_option autoImplicit false
namespace FourCorner

lemma seven_character_two {p : ℕ} [Fact p.Prime] (hp : p % 8 = 7) :
    quadraticChar (ZMod p) 2 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply Ring.two_ne_zero
    simpa only [ZMod.ringChar_zmod_n] using (show p ≠ 2 by omega)
  exact (quadraticChar_one_iff_isSquare h2).mpr
    ((ZMod.exists_sq_eq_two_iff (by omega)).mpr (Or.inr hp))

/-- An adjacent Gaussian displacement has a square norm character at an
inert corner prime. Both possible coordinate axes are included. -/
lemma seven_adjacent_norm_character {p : ℕ} [Fact p.Prime] (hp : p % 8 = 7)
    (x y : ZMod p) (hn : x ^ 2 + y ^ 2 ≠ 0)
    (h : x ^ 2 - y ^ 2 = 0 ∨ 2 * x * y = 0) :
    quadraticChar (ZMod p) (x ^ 2 + y ^ 2) = 1 := by
  rcases h with h | h
  · have hxy : x ^ 2 = y ^ 2 := sub_eq_zero.mp h
    have hy : y ≠ 0 := by
      intro hz
      apply hn
      simp [hxy, hz]
    rw [hxy, show y ^ 2 + y ^ 2 = 2 * y ^ 2 by ring,
      map_mul, seven_character_two hp, quadraticChar_sq_one' hy, mul_one]
  · have h2 : (2 : ZMod p) ≠ 0 := by
      apply Ring.two_ne_zero
      simpa only [ZMod.ringChar_zmod_n] using (show p ≠ 2 by omega)
    rcases (mul_eq_zero.mp h) with hx | hy
    · have hx : x = 0 := (mul_eq_zero.mp hx).resolve_left h2
      have hy : y ≠ 0 := by intro hz; apply hn; simp [hx, hz]
      simpa [hx] using quadraticChar_sq_one' hy
    · have hx : x ≠ 0 := by intro hz; apply hn; simp [hy, hz]
      simpa [hy] using quadraticChar_sq_one' hx

namespace IntegralModel

lemma seven_corner_side_nonzero (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    {i : Bool × Bool} (hi : p ∣ M.cornerClass i) : (M.L : ZMod p) ≠ 0 := by
  intro hz
  have hL : p ∣ M.L.natAbs := Int.natCast_dvd.mp
    ((ZMod.intCast_zmod_eq_zero_iff_dvd M.L p).mp hz)
  exact (Fact.out : p.Prime).ne_one
    (Nat.eq_one_of_dvd_coprimes (M.cornerClass_coprime_side i) hi hL)

lemma seven_corner_radius_nonzero (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 7) {i j : Bool × Bool} (hne : i ≠ j)
    (hi : p ∣ M.cornerClass i) : (M.cornerRadius j : ZMod p) ≠ 0 := by
  intro hz
  have hc : (p : ℤ) ∣ M.cornerClass i := Int.natCast_dvd_natCast.mpr hi
  have hL := M.corner_legs_other_radius_prime_dvd_side hne Fact.out (by omega)
    (dvd_trans hc (M.cornerClass_dvd_cornerX i))
    (dvd_trans hc (M.cornerClass_dvd_cornerY i))
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  exact M.seven_corner_side_nonzero hi
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL)

/-- At the corner prime, division of the radius sum by two has no effect
on its character. This uses the actual integral half-sum. -/
lemma seven_half_sum_character (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    (hp : p % 8 = 7) {i j : Bool × Bool} (hi : p ∣ M.cornerClass i) :
    legendreSym p ((M.cornerRadius i + M.cornerRadius j) / 2) =
      legendreSym p (M.cornerRadius j) := by
  have hz : (M.cornerRadius i : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (dvd_trans (Int.natCast_dvd_natCast.mpr hi) (M.cornerClass_dvd_cornerRadius i))
  have hv := congrArg (fun n : ℤ => (n : ZMod p)) (M.corner_pair_half_sum_integral i j)
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, hz, zero_add] at hv
  have hh := congrArg (quadraticChar (ZMod p)) hv
  rw [map_mul, seven_character_two hp, one_mul] at hh
  exact hh

/-- Reduction of the signed square and positive norm equations of the
canonical Gaussian root at any corner. -/
lemma seven_corner_root_coordinates (M : IntegralModel) (hX : Odd M.X)
    {p : ℕ} [Fact p.Prime] (j : Bool × Bool) :
    ∃ x y : ZMod p,
      (M.cornerX j.1 : ZMod p) = M.cornerClass j * (x ^ 2 - y ^ 2) ∧
      (M.cornerY j.2 : ZMod p) = M.cornerClass j * (2 * x * y) ∧
      (M.cornerRadius j : ZMod p) = M.cornerClass j * (x ^ 2 + y ^ 2) := by
  have hLe : Even M.L := even_iff_two_dvd.mpr
    (Int.dvd_of_emod_eq_zero M.basic_mod_four.1)
  obtain ⟨q, _, hr, hn, _⟩ := M.corner_gaussian_root hX hLe j
  refine ⟨q.re, q.im, ?_, ?_, ?_⟩
  · have hh := congrArg Zsqrtd.re hr
    simp [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul] at hh
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hh
    simpa [pow_two, sub_eq_add_neg] using hc
  · have hh := congrArg Zsqrtd.im hr
    simp [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul] at hh
    have hc := congrArg (fun z : ℤ => (z : ZMod p)) hh
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast] at hc
    linear_combination hc
  · have hh := congrArg (fun z : ℤ => (z : ZMod p)) hn
    simpa [Zsqrtd.norm, pow_two] using hh

lemma seven_corner_coordinates_zero (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    {i : Bool × Bool} (hi : p ∣ M.cornerClass i) :
    (M.cornerX i.1 : ZMod p) = 0 ∧ (M.cornerY i.2 : ZMod p) = 0 := by
  have hc : (p : ℤ) ∣ M.cornerClass i := Int.natCast_dvd_natCast.mpr hi
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (dvd_trans hc (M.cornerClass_dvd_cornerX i)),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (dvd_trans hc (M.cornerClass_dvd_cornerY i))⟩

lemma seven_adjacent_coordinates (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    {i j : Bool × Bool} (hi : p ∣ M.cornerClass i)
    (hd : cornerDistanceSquared i j = 1) :
    (M.cornerX j.1 : ZMod p) = 0 ∨ (M.cornerY j.2 : ZMod p) = 0 := by
  obtain ⟨hx, hy⟩ := M.seven_corner_coordinates_zero hi
  have h : i.1 = j.1 ∨ i.2 = j.2 := by
    rcases i with ⟨e, f⟩
    rcases j with ⟨g, h⟩
    cases e <;> cases f <;> cases g <;> cases h <;>
      norm_num [cornerDistanceSquared] at hd <;> simp
  rcases h with h | h
  · exact Or.inl (h ▸ hx)
  · exact Or.inr (h ▸ hy)

lemma seven_opposite_coordinates (M : IntegralModel) {p : ℕ} [Fact p.Prime]
    {i j : Bool × Bool} (hi : p ∣ M.cornerClass i)
    (hd : cornerDistanceSquared i j = 2) :
    (M.cornerX j.1 : ZMod p) ^ 2 = (M.cornerY j.2 : ZMod p) ^ 2 := by
  obtain ⟨hx, hy⟩ := M.seven_corner_coordinates_zero hi
  rcases i with ⟨e, f⟩
  rcases j with ⟨g, h⟩
  cases e <;> cases f <;> cases g <;> cases h <;>
    norm_num [cornerDistanceSquared] at hd
  all_goals
    simp only [cornerX, cornerY, Bool.false_eq_true, ↓reduceIte, sub_zero,
      Int.cast_sub, sub_eq_zero] at hx hy ⊢
    simp [hx, hy]

/-- The inert branch of manuscript Lemma `profile-ramified-character`.
The square root, its positive norm, and the corner reduction all come from
the actual primitive integral model. -/
theorem corner_ramified_character_seven (M : IntegralModel) (hX : Odd M.X)
    {p : ℕ} [Fact p.Prime] (hp : p % 8 = 7)
    {i j : Bool × Bool} (hne : i ≠ j) (hi : p ∣ M.cornerClass i) :
    legendreSym p ((M.cornerRadius i + M.cornerRadius j) / 2) =
      legendreSym p (M.cornerClass j) *
        ((-1 : ℤ) ^ ((p + 1) / 8)) ^ (cornerDistanceSquared i j - 1).toNat := by
  rw [M.seven_half_sum_character hp hi]
  obtain ⟨x, y, hr, him, hn⟩ := M.seven_corner_root_coordinates hX (p := p) j
  have ha := M.seven_corner_radius_nonzero hp hne hi
  have hm : (M.cornerClass j : ZMod p) ≠ 0 := by
    intro hz
    apply ha
    simp [hz] at hn
    exact hn
  have hnorm : x ^ 2 + y ^ 2 ≠ 0 := by
    intro hz
    apply ha
    simpa [hz] using hn
  have hc : quadraticChar (ZMod p) (x ^ 2 + y ^ 2) =
      ((-1 : ℤ) ^ ((p + 1) / 8)) ^ (cornerDistanceSquared i j - 1).toNat := by
    rcases cornerDistanceSquared_one_or_two hne with hd | hd
    · have haxis : x ^ 2 - y ^ 2 = 0 ∨ 2 * x * y = 0 := by
        rcases M.seven_adjacent_coordinates hi hd with hx | hy
        · rw [hr] at hx
          exact Or.inl ((mul_eq_zero.mp hx).resolve_left hm)
        · rw [him] at hy
          exact Or.inr ((mul_eq_zero.mp hy).resolve_left hm)
      simpa [hd] using seven_adjacent_norm_character hp x y hnorm haxis
    · have heq := M.seven_opposite_coordinates hi hd
      rw [hr, him, mul_pow, mul_pow] at heq
      have heq' := mul_left_cancel₀ (pow_ne_zero 2 hm) heq
      simpa [hd] using seven_opposite_norm_character hp x y hnorm heq'
  change quadraticChar (ZMod p) (M.cornerRadius j) =
    quadraticChar (ZMod p) ((M.cornerClass j : ℤ) : ZMod p) * _
  rw [hn, map_mul, hc]
  simp only [Int.cast_natCast]

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.corner_ramified_character_seven
