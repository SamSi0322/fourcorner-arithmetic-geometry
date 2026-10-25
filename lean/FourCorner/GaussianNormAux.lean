import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring

namespace FourCorner

theorem gaussian_sq_norm_identity (m : ℕ) (q : GaussianInt) (a b : ℤ)
    (h : (⟨a, b⟩ : GaussianInt) = (m : GaussianInt) * q ^ 2) :
    ((m : ℤ) * q.norm) ^ 2 = a ^ 2 + b ^ 2 := by
  have hn := congrArg Zsqrtd.norm h
  simp only [pow_two, Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at hn
  change a * a - (-1) * b * b = (m : ℤ) * m * (q.norm * q.norm) at hn
  calc
    ((m : ℤ) * q.norm) ^ 2 = (m : ℤ) * m * (q.norm * q.norm) := by ring
    _ = a * a - (-1) * b * b := hn.symm
    _ = a ^ 2 + b ^ 2 := by ring

theorem gaussian_norm_pos {q : GaussianInt} (hq : q ≠ 0) : 0 < q.norm :=
  GaussianInt.norm_pos.mpr hq

end FourCorner
