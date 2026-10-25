import FourCorner.VerticalGaussianIdentity
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FourCorner

/-- A positive real square of a Gaussian rational has zero imaginary part,
and therefore has a positive rational square root. -/
theorem positive_rational_gaussian_square {s u v : ℚ} (hs : 0 < s)
    (hre : u ^ 2 - v ^ 2 = s) (him : 2 * u * v = 0) :
    ∃ w : ℚ, 0 < w ∧ s = w ^ 2 := by
  have huv : u * v = 0 := by linarith
  have hv : v = 0 := by
    rcases mul_eq_zero.mp huv with hu | hv
    · rw [hu] at hre
      nlinarith [sq_nonneg v]
    · exact hv
  have hu : u ≠ 0 := by
    intro hu
    simp [hu, hv] at hre
    linarith
  exact ⟨|u|, abs_pos.mpr hu, by simpa [hv, sq_abs] using hre.symm⟩

/-- If `C² = n*s*R²` in Q(i), where `n,s` are positive rationals and
`R` is nonzero, then `s` is `n` times a positive rational square. All
Gaussian coordinates and multiplication identities are explicit. -/
theorem rational_gaussian_square_transfer
    {n s cr ci rr ri : ℚ} (hn : 0 < n) (hs : 0 < s)
    (hR : rr ≠ 0 ∨ ri ≠ 0)
    (hre : cr ^ 2 - ci ^ 2 = n * s * (rr ^ 2 - ri ^ 2))
    (him : 2 * cr * ci = n * s * (2 * rr * ri)) :
    ∃ w : ℚ, 0 < w ∧ s = n * w ^ 2 := by
  let d : ℚ := rr ^ 2 + ri ^ 2
  have hdpos : 0 < d := by
    rcases hR with hr | hi
    · dsimp [d]
      nlinarith [sq_pos_of_ne_zero hr, sq_nonneg ri]
    · dsimp [d]
      nlinarith [sq_pos_of_ne_zero hi, sq_nonneg rr]
  have hd : d ≠ 0 := ne_of_gt hdpos
  let u : ℚ := (cr * rr + ci * ri) / d
  let v : ℚ := (ci * rr - cr * ri) / d
  have huvre : u ^ 2 - v ^ 2 = n * s := by
    dsimp [u, v]
    field_simp
    dsimp [d]
    linear_combination (rr ^ 2 - ri ^ 2) * hre + (2 * rr * ri) * him
  have huvim : 2 * u * v = 0 := by
    dsimp [u, v]
    field_simp
    linear_combination (rr ^ 2 - ri ^ 2) * him - (2 * rr * ri) * hre
  obtain ⟨w, hw, heq⟩ := positive_rational_gaussian_square (mul_pos hn hs) huvre huvim
  refine ⟨w / n, div_pos hw hn, ?_⟩
  have hn0 : n ≠ 0 := ne_of_gt hn
  field_simp
  nlinarith [heq]

/-- A square class of the product across a vertical unit segment determines
 the positive rational square class of the sum of the two norms minus one. -/
theorem vertical_gaussian_squareclass_transfer
    (x y a b n rr ri : ℚ)
    (ha : a ^ 2 = x ^ 2 + y ^ 2)
    (hb : b ^ 2 = x ^ 2 + (y + 1) ^ 2)
    (hn : 0 < n) (hs : 0 < (a + b) ^ 2 - 1)
    (hR : rr ≠ 0 ∨ ri ≠ 0)
    (hre : x ^ 2 - y * (y + 1) = n * (rr ^ 2 - ri ^ 2))
    (him : x * (y + 1) + y * x = n * (2 * rr * ri)) :
    ∃ w : ℚ, 0 < w ∧ (a + b) ^ 2 - 1 = n * w ^ 2 := by
  obtain ⟨hCre, hCim⟩ := vertical_gaussian_identity x y a b ha hb
  apply rational_gaussian_square_transfer (cr := b * x + a * x)
    (ci := b * y + a * (y + 1)) hn hs hR
  · rw [hCre, hre]
    ring
  · rw [hCim, him]
    ring

end FourCorner

#print axioms FourCorner.positive_rational_gaussian_square
#print axioms FourCorner.rational_gaussian_square_transfer

#print axioms FourCorner.vertical_gaussian_squareclass_transfer
