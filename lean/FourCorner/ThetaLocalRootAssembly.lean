import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace FourCorner

/-- Clear the common square denominator in the three normalized theta
radicands. The roots are explicitly obtained by multiplying by `z`. -/
theorem theta_roots_of_normalized_isSquare {K : Type*} [Field K] {z : K}
    (hz : z ≠ 0)
    (hP : IsSquare (1 + 50 * (z⁻¹) ^ 2))
    (hQ : IsSquare (1 + 14 * z⁻¹ + 51 * (z⁻¹) ^ 2))
    (hR : IsSquare (1 - 14 * z⁻¹ + 51 * (z⁻¹) ^ 2)) :
    ∃ P Q R : K, P ^ 2 = z ^ 2 + 50 ∧
      Q ^ 2 = z ^ 2 + 14 * z + 51 ∧
      R ^ 2 = z ^ 2 - 14 * z + 51 := by
  obtain ⟨p, hp⟩ := hP.exists_sq
  obtain ⟨q, hq⟩ := hQ.exists_sq
  obtain ⟨r, hr⟩ := hR.exists_sq
  refine ⟨z * p, z * q, z * r, ?_, ?_, ?_⟩
  · rw [mul_pow, ← hp]
    field_simp
  · rw [mul_pow, ← hq]
    field_simp
  · rw [mul_pow, ← hr]
    field_simp

#print axioms theta_roots_of_normalized_isSquare

end FourCorner
