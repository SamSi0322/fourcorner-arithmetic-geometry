import FourCorner.GaussianCorners
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

namespace FourCorner

/-- Equality of the complex realizations of two rational Gaussian coordinates
is exactly equality of the two rational coordinate pairs. -/
lemma rational_gaussian_embedding_eq_iff {a b c d : ℚ} :
    (a : ℂ) + (b : ℂ) * Complex.I = (c : ℂ) + (d : ℂ) * Complex.I ↔
      a = c ∧ b = d := by
  rw [Complex.ext_iff]
  simp

/-- The coordinate encoding of a rational Gaussian number has the same
nonzero condition as its complex realization. -/
lemma rational_gaussian_embedding_ne_zero_iff {u v : ℚ} :
    (u : ℂ) + (v : ℂ) * Complex.I ≠ 0 ↔ u ≠ 0 ∨ v ≠ 0 := by
  have hz : (u : ℂ) + (v : ℂ) * Complex.I = 0 ↔ u = 0 ∧ v = 0 := by
    rw [Complex.ext_iff]
    simp
  rw [ne_eq, hz]
  exact not_and_or

/-- Complex multiplication agrees with the rational-coordinate formula for
a scalar times a Gaussian square. -/
lemma rational_gaussian_embedding_square (u v s : ℚ) :
    (s : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 =
      ((s * (u ^ 2 - v ^ 2) : ℚ) : ℂ) +
      ((s * (2 * u * v) : ℚ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring_nf
  simp

/-- The coordinate definition is equivalent to literal multiplication by a
nonzero square in the rational Gaussian subfield of the complex numbers.
The witness remains a pair of rationals, so the square lies in Q(i). -/
theorem gaussian_squareclass_iff_complex (a b s : ℚ) :
    GaussianRationalSquareClass a b s ↔
      s ≠ 0 ∧ ∃ u v : ℚ,
        ((u : ℂ) + (v : ℂ) * Complex.I) ≠ 0 ∧
        (a : ℂ) + (b : ℂ) * Complex.I =
          (s : ℂ) * ((u : ℂ) + (v : ℂ) * Complex.I) ^ 2 := by
  constructor
  · rintro ⟨hs, u, v, huv, ha, hb⟩
    refine ⟨hs, u, v, rational_gaussian_embedding_ne_zero_iff.mpr huv, ?_⟩
    rw [rational_gaussian_embedding_square, ← ha, ← hb]
  · rintro ⟨hs, u, v, huv, heq⟩
    rw [rational_gaussian_embedding_square] at heq
    obtain ⟨ha, hb⟩ := rational_gaussian_embedding_eq_iff.mp heq
    exact ⟨hs, u, v, rational_gaussian_embedding_ne_zero_iff.mp huv, ha, hb⟩

/-- A represented squareclass is a nonzero rational Gaussian number. -/
theorem GaussianRationalSquareClass.complex_ne_zero {a b s : ℚ}
    (h : GaussianRationalSquareClass a b s) :
    (a : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
  obtain ⟨hs, u, v, huv, heq⟩ := (gaussian_squareclass_iff_complex a b s).mp h
  rw [heq]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  exact mul_ne_zero hsC (pow_ne_zero 2 huv)

/-- The nonzero condition is also available directly in rational coordinates. -/
theorem GaussianRationalSquareClass.coordinates_ne_zero {a b s : ℚ}
    (h : GaussianRationalSquareClass a b s) : a ≠ 0 ∨ b ≠ 0 :=
  rational_gaussian_embedding_ne_zero_iff.mp h.complex_ne_zero

end FourCorner

#print axioms FourCorner.gaussian_squareclass_iff_complex
#print axioms FourCorner.GaussianRationalSquareClass.complex_ne_zero
#print axioms FourCorner.GaussianRationalSquareClass.coordinates_ne_zero
