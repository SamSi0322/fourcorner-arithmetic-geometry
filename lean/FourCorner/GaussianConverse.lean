import FourCorner.RadiusModel
import FourCorner.GaussianNormAux
import Mathlib.Tactic.FieldSimp

namespace FourCorner

/-- The positive rational distance furnished by a scaled Gaussian square. -/
def gaussianRadius (L : ℤ) (m : ℕ) (q : GaussianInt) : ℚ :=
  (m : ℚ) * (q.norm : ℚ) / (L : ℚ)

theorem gaussianRadius_pos {L : ℤ} {m : ℕ} {q : GaussianInt}
    (hL : 0 < L) (hm : 0 < m) (hq : q ≠ 0) :
    0 < gaussianRadius L m q := by
  apply div_pos
  · apply mul_pos
    · exact_mod_cast hm
    · exact_mod_cast gaussian_norm_pos hq
  · exact_mod_cast hL

/-- Taking norms proves the rational distance identity without assuming it. -/
theorem gaussianRadius_sq (L a b : ℤ) (m : ℕ) (q : GaussianInt)
    (h : (⟨a, b⟩ : GaussianInt) = (m : GaussianInt) * q ^ 2) :
    (gaussianRadius L m q) ^ 2 = ((a : ℚ) / L) ^ 2 + ((b : ℚ) / L) ^ 2 := by
  simp only [gaussianRadius, div_pow, ← add_div]
  congr 1
  exact_mod_cast gaussian_sq_norm_identity m q a b h

/-- Four actual Gaussian square equations imply a strict rational point.
The corner order is `(false,false), (true,false), (false,true), (true,true)`. -/
theorem gaussian_corners_to_strict_point
    (L X Y : ℤ) (m : Bool × Bool → ℕ) (q : Bool × Bool → GaussianInt)
    (hL : 0 < L) (hX : 0 < X) (hXL : X < L) (hY : 0 < Y) (hYL : Y < L)
    (hm : ∀ c, 0 < m c) (hq : ∀ c, q c ≠ 0)
    (hroot : ∀ c : Bool × Bool,
      (⟨X - (if c.1 then L else 0), Y - (if c.2 then L else 0)⟩ : GaussianInt) =
        (m c : GaussianInt) * (q c) ^ 2) :
    StrictPoint ((X : ℚ) / L) ((Y : ℚ) / L)
      (gaussianRadius L (m (false, false)) (q (false, false)))
      (gaussianRadius L (m (true, false)) (q (true, false)))
      (gaussianRadius L (m (false, true)) (q (false, true)))
      (gaussianRadius L (m (true, true)) (q (true, true))) := by
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hLn : (L : ℚ) ≠ 0 := ne_of_gt hLq
  have hr : ∀ c, 0 < gaussianRadius L (m c) (q c) :=
    fun c => gaussianRadius_pos hL (hm c) (hq c)
  refine ⟨div_pos (by exact_mod_cast hX) hLq,
    (div_lt_one hLq).2 (by exact_mod_cast hXL),
    div_pos (by exact_mod_cast hY) hLq,
    (div_lt_one hLq).2 (by exact_mod_cast hYL),
    hr _, hr _, hr _, hr _, ?_⟩
  have hs (c : Bool × Bool) :
      gaussianRadius L (m c) (q c) ^ 2 =
        (((X - (if c.1 then L else 0) : ℤ) : ℚ) / L) ^ 2 +
        (((Y - (if c.2 then L else 0) : ℤ) : ℚ) / L) ^ 2 :=
    gaussianRadius_sq L _ _ (m c) (q c) (hroot c)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hs (false, false)
  · rw [hs (true, false)]
    simp only [↓reduceIte, Bool.false_eq_true, sub_zero, Int.cast_sub]
    field_simp
    ring
  · rw [hs (false, true)]
    simp only [↓reduceIte, Bool.false_eq_true, sub_zero, Int.cast_sub]
    field_simp
    ring
  · rw [hs (true, true)]
    simp only [↓reduceIte, Int.cast_sub]
    field_simp
    ring

/-- Strict coordinates force every root to be nonzero, so no separate
nonvanishing assumption is needed in the converse. -/
theorem gaussian_corners_to_strict_point_of_roots
    (L X Y : ℤ) (m : Bool × Bool → ℕ) (q : Bool × Bool → GaussianInt)
    (hL : 0 < L) (hX : 0 < X) (hXL : X < L) (hY : 0 < Y) (hYL : Y < L)
    (hm : ∀ c, 0 < m c)
    (hroot : ∀ c : Bool × Bool,
      (⟨X - (if c.1 then L else 0), Y - (if c.2 then L else 0)⟩ : GaussianInt) =
        (m c : GaussianInt) * (q c) ^ 2) :
    StrictPoint ((X : ℚ) / L) ((Y : ℚ) / L)
      (gaussianRadius L (m (false, false)) (q (false, false)))
      (gaussianRadius L (m (true, false)) (q (true, false)))
      (gaussianRadius L (m (false, true)) (q (false, true)))
      (gaussianRadius L (m (true, true)) (q (true, true))) := by
  have hq (c : Bool × Bool) : q c ≠ 0 := by
    intro hz
    have he := hroot c
    rw [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] at he
    have hr := congrArg Zsqrtd.re he
    change X - (if c.1 then L else 0) = 0 at hr
    cases hc : c.1 <;> simp [hc] at hr <;> omega
  exact gaussian_corners_to_strict_point L X Y m q hL hX hXL hY hYL hm hq hroot

#print axioms gaussian_sq_norm_identity
#print axioms gaussianRadius_sq
#print axioms gaussian_corners_to_strict_point
#print axioms gaussian_corners_to_strict_point_of_roots

end FourCorner
