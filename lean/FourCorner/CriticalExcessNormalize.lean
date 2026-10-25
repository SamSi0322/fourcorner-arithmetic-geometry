import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace FourCorner

/-- Normalize a square pattern whose zeroth radius is zero. -/
theorem critical_zero_origin_normalize {F : Type*} [Field F]
    (a₀ a₁ a₂ a₃ i c b : F) (_hi : i ^ 2 = -1) (hb : b ≠ 0)
    (h₀ : a₀ ^ 2 = c) (h₁ : a₁ ^ 2 = c + b)
    (h₂ : a₂ ^ 2 = c + i * b) (h₃ : a₃ ^ 2 = c + (1 + i) * b)
    (hz : a₀ = 0)
    (hQ : IsSquare (a₀ * a₃ + a₁ * a₂) ∨
      IsSquare (2 * (a₀ * a₃ + a₁ * a₂))) :
    ∃ u v : F, u ^ 2 = i ∧ v ^ 2 = 1 + i ∧
      (IsSquare u ∨ IsSquare (2 * u)) := by
  have hc : c = 0 := by simpa [hz] using h₀.symm
  have ha₁ : a₁ ≠ 0 := by
    intro hv
    exact hb (by simpa [hc, hv] using h₁.symm)
  refine ⟨a₂ / a₁, a₃ / a₁, ?_, ?_, ?_⟩
  · rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 ha₁)).mpr
    rw [h₁, h₂, hc]
    ring
  · rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 ha₁)).mpr
    rw [h₁, h₃, hc]
    ring
  · have hquot : (a₀ * a₃ + a₁ * a₂) / a₁ ^ 2 = a₂ / a₁ := by
      rw [hz]
      field_simp
      ring
    rcases hQ with hQ | hQ
    · exact Or.inl (hquot ▸ hQ.div (IsSquare.sq a₁))
    · have hquot₂ : (2 * (a₀ * a₃ + a₁ * a₂)) / a₁ ^ 2 =
          2 * (a₂ / a₁) := by rw [mul_div_assoc, hquot]
      exact Or.inr (hquot₂ ▸ hQ.div (IsSquare.sq a₁))

/-- A zero corner in the critical four-square pattern yields the normalized
square conditions after relabelling the square. The opposite-product sum is
preserved by all four relabellings. -/
theorem critical_zero_corner_normalize {F : Type*} [Field F]
    (a₀ a₁ a₂ a₃ i c b : F)
    (hi : i ^ 2 = -1) (hb : b ≠ 0)
    (h₀ : a₀ ^ 2 = c) (h₁ : a₁ ^ 2 = c + b)
    (h₂ : a₂ ^ 2 = c + i * b) (h₃ : a₃ ^ 2 = c + (1 + i) * b)
    (hz : a₀ = 0 ∨ a₁ = 0 ∨ a₂ = 0 ∨ a₃ = 0)
    (hQ : IsSquare (a₀ * a₃ + a₁ * a₂) ∨
      IsSquare (2 * (a₀ * a₃ + a₁ * a₂))) :
    ∃ u v jota : F, jota ^ 2 = -1 ∧ u ^ 2 = jota ∧
      v ^ 2 = 1 + jota ∧ (IsSquare u ∨ IsSquare (2 * u)) := by
  have hni : (-i) ^ 2 = -1 := by simpa using hi
  have hnb : -b ≠ 0 := neg_ne_zero.mpr hb
  rcases hz with hz | hz | hz | hz
  · obtain ⟨u, v, hu, hv, hs⟩ :=
      critical_zero_origin_normalize a₀ a₁ a₂ a₃ i c b hi hb h₀ h₁ h₂ h₃ hz hQ
    exact ⟨u, v, i, hi, hu, hv, hs⟩
  · have h₁' : a₀ ^ 2 = (c + b) + -b := by linear_combination h₀
    have h₂' : a₃ ^ 2 = (c + b) + (-i) * (-b) := by linear_combination h₃
    have h₃' : a₂ ^ 2 = (c + b) + (1 + -i) * (-b) := by linear_combination h₂
    have hQ' : IsSquare (a₁ * a₂ + a₀ * a₃) ∨
        IsSquare (2 * (a₁ * a₂ + a₀ * a₃)) := by
      simpa only [add_comm] using hQ
    obtain ⟨u, v, hu, hv, hs⟩ := critical_zero_origin_normalize
      a₁ a₀ a₃ a₂ (-i) (c + b) (-b) hni hnb h₁ h₁' h₂' h₃' hz hQ'
    exact ⟨u, v, -i, hni, hu, hv, hs⟩
  · have h₁' : a₃ ^ 2 = (c + i * b) + b := by linear_combination h₃
    have h₂' : a₀ ^ 2 = (c + i * b) + (-i) * b := by linear_combination h₀
    have h₃' : a₁ ^ 2 = (c + i * b) + (1 + -i) * b := by linear_combination h₁
    have hQ' : IsSquare (a₂ * a₁ + a₃ * a₀) ∨
        IsSquare (2 * (a₂ * a₁ + a₃ * a₀)) := by
      simpa only [mul_comm, add_comm] using hQ
    obtain ⟨u, v, hu, hv, hs⟩ := critical_zero_origin_normalize
      a₂ a₃ a₀ a₁ (-i) (c + i * b) b hni hb h₂ h₁' h₂' h₃' hz hQ'
    exact ⟨u, v, -i, hni, hu, hv, hs⟩
  · have h₁' : a₂ ^ 2 = (c + (1 + i) * b) + -b := by linear_combination h₂
    have h₂' : a₁ ^ 2 = (c + (1 + i) * b) + i * (-b) := by linear_combination h₁
    have h₃' : a₀ ^ 2 = (c + (1 + i) * b) + (1 + i) * (-b) := by
      linear_combination h₀
    have hQ' : IsSquare (a₃ * a₀ + a₂ * a₁) ∨
        IsSquare (2 * (a₃ * a₀ + a₂ * a₁)) := by
      simpa only [mul_comm] using hQ
    obtain ⟨u, v, hu, hv, hs⟩ := critical_zero_origin_normalize
      a₃ a₂ a₁ a₀ i (c + (1 + i) * b) (-b) hi hnb h₃ h₁' h₂' h₃' hz hQ'
    exact ⟨u, v, i, hi, hu, hv, hs⟩

end FourCorner

#print axioms FourCorner.critical_zero_origin_normalize
#print axioms FourCorner.critical_zero_corner_normalize
