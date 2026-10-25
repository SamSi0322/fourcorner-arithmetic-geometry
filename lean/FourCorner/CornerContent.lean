import FourCorner.IntegralModel
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace FourCorner
namespace IntegralModel

/-- Signed horizontal leg at the corner selected by `e`. -/
def cornerX (M : IntegralModel) (e : Bool) : ℤ := M.X - if e then M.L else 0

/-- Signed vertical leg at the corner selected by `h`. -/
def cornerY (M : IntegralModel) (h : Bool) : ℤ := M.Y - if h then M.L else 0

/-- Canonical positive content of a corner's two signed legs. -/
def cornerContent (M : IntegralModel) (c : Bool × Bool) : ℕ :=
  Int.gcd (M.cornerX c.1) (M.cornerY c.2)

/-- The distance to the indexed corner, retained from the original model. -/
def cornerRadius (M : IntegralModel) (c : Bool × Bool) : ℤ :=
  match c with
  | (false, false) => M.A₀
  | (true, false) => M.A₁
  | (false, true) => M.A₂
  | (true, true) => M.A₃

lemma corner_sq (M : IntegralModel) (c : Bool × Bool) :
    M.cornerRadius c ^ 2 = M.cornerX c.1 ^ 2 + M.cornerY c.2 ^ 2 := by
  rcases c with ⟨e, h⟩
  cases e <;> cases h <;> simp only [cornerRadius, cornerX, cornerY, Bool.false_eq_true,
    ↓reduceIte, sub_zero]
  · exact M.sq₀
  · rw [M.sq₂]; ring
  · rw [M.sq₁]; ring
  · rw [M.sq₃]; ring

lemma cornerRadius_pos (M : IntegralModel) (c : Bool × Bool) :
    0 < M.cornerRadius c := by
  rcases c with ⟨e, h⟩
  cases e <;> cases h <;> simp only [cornerRadius]
  · exact M.A₀_pos
  · exact M.A₂_pos
  · exact M.A₁_pos
  · exact M.A₃_pos

lemma cornerX_ne_zero (M : IntegralModel) (e : Bool) : M.cornerX e ≠ 0 := by
  cases e <;> simp only [cornerX, Bool.false_eq_true, ↓reduceIte, sub_zero]
  · exact ne_of_gt M.X_pos
  · exact sub_ne_zero.mpr (ne_of_lt M.X_lt)

lemma cornerY_ne_zero (M : IntegralModel) (h : Bool) : M.cornerY h ≠ 0 := by
  cases h <;> simp only [cornerY, Bool.false_eq_true, ↓reduceIte, sub_zero]
  · exact ne_of_gt M.Y_pos
  · exact sub_ne_zero.mpr (ne_of_lt M.Y_lt)

lemma cornerContent_pos (M : IntegralModel) (c : Bool × Bool) :
    0 < M.cornerContent c :=
  Int.gcd_pos_of_ne_zero_left _ (M.cornerX_ne_zero c.1)

lemma cornerContent_dvd_X (M : IntegralModel) (c : Bool × Bool) :
    (M.cornerContent c : ℤ) ∣ M.cornerX c.1 := Int.gcd_dvd_left _ _

lemma cornerContent_dvd_Y (M : IntegralModel) (c : Bool × Bool) :
    (M.cornerContent c : ℤ) ∣ M.cornerY c.2 := Int.gcd_dvd_right _ _

lemma cornerX_odd (M : IntegralModel) (hX : Odd M.X) (hL : Even M.L)
    (e : Bool) : Odd (M.cornerX e) := by
  cases e <;> simp only [cornerX, Bool.false_eq_true, ↓reduceIte, sub_zero]
  · exact hX
  · exact hX.sub_even hL

lemma cornerContent_odd (M : IntegralModel) (hX : Odd M.X) (hL : Even M.L)
    (c : Bool × Bool) : Odd (M.cornerContent c) :=
  (Int.natAbs_odd.mpr (M.cornerX_odd hX hL c.1)).of_dvd_nat
    (Int.natCast_dvd.mp (M.cornerContent_dvd_X c))

/-- Primitivity applies to divisors of the two legs at any corner and the side. -/
lemma common_corner_divisor_eq_one (M : IntegralModel) (c : Bool × Bool) {p : ℕ}
    (hX : (p : ℤ) ∣ M.cornerX c.1) (hY : (p : ℤ) ∣ M.cornerY c.2)
    (hL : (p : ℤ) ∣ M.L) : p = 1 := by
  have hx : (p : ℤ) ∣ M.X := by
    cases he : c.1
    · simpa [cornerX, he] using hX
    · simpa [cornerX, he] using dvd_add hX hL
  have hy : (p : ℤ) ∣ M.Y := by
    cases hh : c.2
    · simpa [cornerY, hh] using hY
    · simpa [cornerY, hh] using dvd_add hY hL
  have hd : p ∣ Nat.gcd (Nat.gcd M.X.natAbs M.Y.natAbs) M.L.natAbs :=
    Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hx) (Int.natCast_dvd.mp hy))
      (Int.natCast_dvd.mp hL)
  rw [M.primitive] at hd
  exact Nat.dvd_one.mp hd

lemma cornerContent_coprime_side (M : IntegralModel) (c : Bool × Bool) :
    Nat.Coprime (M.cornerContent c) M.L.natAbs := by
  apply M.common_corner_divisor_eq_one c
  · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))
      (M.cornerContent_dvd_X c)
  · exact dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _))
      (M.cornerContent_dvd_Y c)
  · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)

private lemma dvd_side_of_different_bits {p z L : ℤ} {e e' : Bool} (hne : e ≠ e')
    (he : p ∣ z - if e then L else 0) (he' : p ∣ z - if e' then L else 0) :
    p ∣ L := by
  cases e <;> cases e'
  · exact (hne rfl).elim
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at he he'
    have hid : z - (z - L) = L := by ring
    rw [← hid]
    exact dvd_sub he he'
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at he he'
    have hid : z - (z - L) = L := by ring
    rw [← hid]
    exact dvd_sub he' he
  · exact (hne rfl).elim

/-- Distinct corners have coprime canonical contents, including opposite corners. -/
lemma cornerContent_pairwise_coprime (M : IntegralModel) {c c' : Bool × Bool}
    (hne : c ≠ c') : Nat.Coprime (M.cornerContent c) (M.cornerContent c') := by
  let p := Nat.gcd (M.cornerContent c) (M.cornerContent c')
  have hpc : (p : ℤ) ∣ M.cornerContent c :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hpc' : (p : ℤ) ∣ M.cornerContent c' :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  have hx := dvd_trans hpc (M.cornerContent_dvd_X c)
  have hy := dvd_trans hpc (M.cornerContent_dvd_Y c)
  apply M.common_corner_divisor_eq_one c hx hy
  by_cases he : c.1 = c'.1
  · have hh : c.2 ≠ c'.2 := fun hh => hne (Prod.ext he hh)
    exact dvd_side_of_different_bits hh hy
      (dvd_trans hpc' (M.cornerContent_dvd_Y c'))
  · exact dvd_side_of_different_bits he hx
      (dvd_trans hpc' (M.cornerContent_dvd_X c'))

/-- Every corner content divides the product of the two diagonal linear forms. -/
lemma cornerContent_dvd_diagonal_product (M : IntegralModel) (c : Bool × Bool) :
    (M.cornerContent c : ℤ) ∣ (M.X - M.Y) * (M.X + M.Y - M.L) := by
  have hx := M.cornerContent_dvd_X c
  have hy := M.cornerContent_dvd_Y c
  rcases c with ⟨e, h⟩
  cases e <;> cases h <;>
    simp only [cornerX, cornerY, Bool.false_eq_true, ↓reduceIte, sub_zero] at hx hy
  · exact dvd_mul_of_dvd_left (dvd_sub hx hy) _
  · exact dvd_mul_of_dvd_right (by simpa [sub_eq_add_neg, add_assoc] using dvd_add hx hy) _
  · have heq : M.X - M.L + M.Y = M.X + M.Y - M.L := by ring
    exact dvd_mul_of_dvd_right (by rw [← heq]; exact dvd_add hx hy) _
  · have heq : (M.X - M.L) - (M.Y - M.L) = M.X - M.Y := by ring
    exact dvd_mul_of_dvd_left (by rw [← heq]; exact dvd_sub hx hy) _

end IntegralModel
end FourCorner

#print axioms FourCorner.IntegralModel.cornerContent_odd
#print axioms FourCorner.IntegralModel.cornerContent_coprime_side
#print axioms FourCorner.IntegralModel.cornerContent_pairwise_coprime

#print axioms FourCorner.IntegralModel.cornerContent_dvd_diagonal_product
